/* pl2detlog fast Detlog engine: a closure-compiled deterministic interpreter.
   Determinism is what makes it fast:
   - each clause is compiled once into closures (no copying of clause bodies at call time);
   - heads are matched WAM-style: a first-occurrence head variable takes the argument itself,
     so nothing is copied or bound to enter a clause;
   - a call selects its clause by first argument and commits: no choicepoint, no retry, and the
     trail is only consulted by if_commit/3 conditions;
   - the generated packet loops ( nm([],[]).  nm([I|Is],O) :- nmr(I,O1), nm(Is,O2), rows_concat([O1,O2],O). )
     run as native loops in linear time.
   Its answers are those of the reference Detlog engine (detlog_engine.js); a run that exhausts the JS
   stack falls back to it. */
(function (P) {
  if (!P.nativeBatch && typeof require === 'function') require('./native.js');
  'use strict';
  const { Var, Cmp, NIL, list, deref, listToArray, termVars } = P;
  const D = deref;

  function FastDetlog(prog, opts) {
    this.prog = prog; this.opts = opts || {};
    this.preds = new Map();      // key -> {fn}
    const self = this;
    for (const [k, cls] of prog.preds) this.ref(k).fn = this.compilePred(k, cls);
  }
  FastDetlog.prototype.ref = function (k) { let r = this.preds.get(k); if (!r) { r = { fn: null, k }; this.preds.set(k, r); } return r; };

  // the machine state lives on a DetEngine (trail, unify, steps, memo, output), so runtime builtins are shared
  FastDetlog.prototype.compilePred = function (k, cls) {
    const self = this;
    const loop = this.loopIdiom(k, cls);
    if (loop) return loop;
    const cc = cls.map(cl => this.compileClause(cl));
    const n = cls[0] && D(cls[0].head).t === 'c' ? D(cls[0].head).a.length : 0;
    // first-argument index: key -> clause list (clauses with a variable first argument go everywhere, in order)
    const keyOf = t => { t = D(t); return t.t === 'c' ? 'c' + t.f + '/' + t.a.length : t.t === 'a' ? 'a' + t.n : t.t === 'n' ? 'n' + t.v + (t.f ? 'f' : '') : t.t === 's' ? 's' + t.v : null; };
    const heads = cls.map(cl => n ? keyOf(D(cl.head).a[0]) : null);
    const index = new Map(); const varIdx = [];
    heads.forEach((h, i) => { if (h === null) varIdx.push(i); });
    for (const h of new Set(heads.filter(x => x !== null))) index.set(h, heads.map((x, i) => (x === h || x === null) ? i : -1).filter(i => i >= 0));
    const all = cc.map((_, i) => i);
    const single = cc.length === 1 ? cc[0] : null;
    return function (args, E) {
      E.tick();
      let cand;
      if (single) cand = null;
      else if (!n) cand = all;
      else {
        const a0 = D(args[0]);
        if (a0.t === 'v') cand = all;
        else cand = index.get(keyOf(a0)) || varIdx;
        if (cand.length > 1 && E.violations.length < 1000) E.violations.push(k);
      }
      if (single) {
        const env = new Array(single.nslots); const m = E.trail.length;
        if (single.head(args, env, E)) return single.body(env, E);
        E.undo(m); return false;
      }
      for (let j = 0; j < cand.length; j++) {
        const c = cc[cand[j]];
        const env = new Array(c.nslots); const m = E.trail.length;
        if (c.head(args, env, E)) return c.body(env, E);
        E.undo(m);
      }
      return false;
    };
  };

  FastDetlog.prototype.compileClause = function (cl) {
    const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
    const vars = termVars(Cmp('-', [cl.head, cl.body]));
    const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
    const seen = new Set();
    const matchers = hargs.map(h => this.compileMatch(h, slot, seen));
    const nh = matchers.length;
    const headFn = nh === 0 ? () => true : function (args, env, E) { for (let i = 0; i < nh; i++) if (!matchers[i](args[i], env, E)) return false; return true; };
    const body = this.compileGoal(cl.body, slot);
    return { head: headFn, body, nslots: vars.length };
  };

  function isGroundTerm(t) { return P.isGround(t); }
  function markGround(t) { t = D(t); if (t.t === 'c' && !t.gr) { t.gr = true; t.a.forEach(markGround); } }
  FastDetlog.prototype.compileBuild = function (t, slot) {
    t = D(t);
    if (t.t === 'v') { const i = slot.get(t); const nm = t.name; return env => env[i] || (env[i] = Var(nm)); }
    if (t.t !== 'c' || isGroundTerm(t)) { if (t.t === 'c') markGround(t); return () => t; }
    const f = t.f, bs = t.a.map(x => this.compileBuild(x, slot)), n = bs.length;
    if (n === 2) { const b0 = bs[0], b1 = bs[1]; return env => ({ t: 'c', f, a: [b0(env), b1(env)] }); }
    return env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = bs[i](env); return { t: 'c', f, a }; };
  };
  FastDetlog.prototype.compileMatch = function (h, slot, seen) {
    h = D(h);
    if (h.t === 'v') {
      const i = slot.get(h);
      if (!seen.has(h)) { seen.add(h); return (a, env) => { env[i] = a; return true; }; }
      return (a, env, E) => E.unify(env[i], a);
    }
    if (h.t === 'a') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a === h || (a.t === 'a' && a.n === h.n); };
    if (h.t === 'n') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a.t === 'n' && a.v === h.v && a.f === h.f; };
    if (h.t === 's') return (a, env, E) => { a = D(a); if (a.t === 'v') { E.bind(a, h); return true; } return a.t === 's' && a.v === h.v; };
    // compound: build it when the argument is a variable, otherwise match argument by argument
    const build = this.compileBuild(h, slot);
    const subs = h.a.map(x => this.compileMatch(x, slot, seen));
    const f = h.f, n = h.a.length;
    return (a, env, E) => {
      a = D(a);
      if (a.t === 'v') { E.bind(a, build(env)); return true; }
      if (a.t !== 'c' || a.f !== f || a.a.length !== n) return false;
      for (let i = 0; i < n; i++) if (!subs[i](a.a[i], env, E)) return false;
      return true;
    };
  };

  FastDetlog.prototype.compileGoal = function (g, slot) {
    g = D(g);
    const self = this;
    const k = P.key(g);
    if (k === ',/2') {
      const gs = P.flatConj(g).map(x => this.compileGoal(x, slot)); const n = gs.length;
      return (env, E) => { for (let i = 0; i < n; i++) if (!gs[i](env, E)) return false; return true; };
    }
    if (k === 'true/0') return (env, E) => { E.tick(); return true; };
    if (k === 'fail/0' || k === 'false/0') return (env, E) => { E.tick(); return false; };
    if (k === 'if_commit/3') {
      const C = this.compileGoal(g.a[0], slot), T = this.compileGoal(g.a[1], slot), F = this.compileGoal(g.a[2], slot);
      return (env, E) => { E.tick(); E.decisions++; const m = E.trail.length; if (C(env, E)) return T(env, E); E.undo(m); return F(env, E); };
    }
    if (k === '=/2') { // inline unification
      const a = this.compileBuild(g.a[0], slot), b = this.compileBuild(g.a[1], slot);
      return (env, E) => { E.tick(); const m = E.trail.length; if (E.unify(a(env), b(env))) return true; E.undo(m); return false; };
    }
    const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
    const build = env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return a; };
    if (this.prog.preds.has(k)) {
      const r = this.ref(k);
      return (env, E) => r.fn(build(env), E);
    }
    const rb = P.DETLOG_RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null);
    if (rb) return (env, E) => { E.tick(); const a = build(env); const m = E.trail.length; if (rb(a, E)) return true; E.undo(m); return false; };
    return () => { throw new Error('Detlog engine: unknown procedure ' + k); };
  };

  // the generated packet loop, run as a native loop
  FastDetlog.prototype.loopIdiom = function (k, cls) {
    const sh = loopShape(k, cls); if (!sh) return null;
    const r = this.ref(sh.callKey), cutVariant = sh.cutVariant;
    return function (args, E) {
      E.tick();
      const items = listToArray(args[0]);
      if (!items) return false;
      const out = [];
      for (let i = 0; i < items.length; i++) {
        E.tick(2);
        const Ov = Var();
        if (!r.fn([items[i], Ov], E)) return false;
        const o1 = listToArray(Ov); E.tick(o1.length);
        let hasCut = false;
        for (const x of o1) { out.push(x); if (cutVariant && D(x).t === 'a' && D(x).n === 'cut') hasCut = true; }
        if (cutVariant && hasCut) { const it = D(items[i]); if (it.t === 'c' && it.f === 'e') break; }
      }
      return E.unify(args[1], list(out));
    };
  };
  function loopShape(k, cls) {
    if (cls.length !== 2 || !/\/2$/.test(k)) return null;
    const [c1, c2] = cls.map(c => ({ h: D(c.head), b: P.flatConj(c.body).map(D) }));
    const nm = c1.h.f;
    if (!(P.isNil(D(c1.h.a[0])) && P.isNil(D(c1.h.a[1])) && c1.b.length === 1 && P.key(c1.b[0]) === 'true/0')) return null;
    const h0 = D(c2.h.a[0]); if (!(P.isCons(h0) && D(h0.a[0]).t === 'v' && D(h0.a[1]).t === 'v')) return null;
    const I = D(h0.a[0]), Is = D(h0.a[1]), O = D(c2.h.a[1]); if (O.t !== 'v') return null;
    const b = c2.b; if (b.length < 2) return null;
    const call = b[0]; if (call.t !== 'c' || call.a.length !== 2 || D(call.a[0]) !== I || D(call.a[1]).t !== 'v') return null;
    const O1 = D(call.a[1]);
    const isRec = (g, O2) => g.t === 'c' && g.f === nm && g.a.length === 2 && D(g.a[0]) === Is && D(g.a[1]) === O2;
    const isCat = (g, O2, Out) => { if (P.key(g) !== 'rows_concat/2') return false; const l = listToArray(g.a[0]); return l && l.length === 2 && D(l[0]) === O1 && D(l[1]) === O2 && D(g.a[1]) === Out; };
    let cutVariant = false;
    if (b.length === 3) { const O2 = D(b[1].a && b[1].a[1]); if (!(isRec(b[1], O2) && isCat(b[2], O2, O))) return null; }
    else if (b.length === 2 && P.key(b[1]) === 'if_commit/3') {
      const ic = b[1]; const cnd = D(ic.a[0]), t = D(ic.a[1]), e = P.flatConj(ic.a[2]).map(D);
      if (!(P.key(cnd) === 'cut_in/2' && D(cnd.a[0]) === I && D(cnd.a[1]) === O1 && P.key(t) === '=/2' && D(t.a[0]) === O && D(t.a[1]) === O1 && e.length === 2)) return null;
      const O2 = D(e[0].a && e[0].a[1]); if (!(isRec(e[0], O2) && isCat(e[1], O2, O))) return null;
      cutVariant = true;
    } else return null;
    return { callKey: P.key(call), cutVariant };
  }

  // ---------------- JIT: Detlog compiled to JavaScript source ----------------
  // One JS function per predicate with positional arguments; clause variables are JS locals; heads are matched
  // inline; if_commit/3 is a labelled block.  Step counts, clause selection and violation counts are those of the
  // closure compiler above, which remains the fallback.
  function jitCompile(prog) {
    const consts = [], constIdx = new Map();
    const K = t => { let i = constIdx.get(t); if (i === undefined) { i = consts.length; consts.push(t); constIdx.set(t, i); } return 'K[' + i + ']'; };
    const rbs = [], rbIdx = new Map();
    const RBf = k => { let i = rbIdx.get(k); if (i === undefined) { const f = P.DETLOG_RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null); if (!f) return null; i = rbs.length; rbs.push(f); rbIdx.set(k, i); } return 'RB[' + i + ']'; };
    const fname = new Map(); let pi = 0;
    for (const k of prog.preds.keys()) fname.set(k, 'p' + (pi++));
    const arityOf = k => +k.slice(k.lastIndexOf('/') + 1);
    let lab = 0;
    let mentioned = new Set(); // variables that occur textually before the goal being compiled
    const out = [];
    const TICK = 'if (++E.steps > E.stepLimit) OVER(E);';
    function keyTest(h, x) {
      if (h.t === 'v') return 'true';
      if (h.t === 'a') return x + ' === ' + K(h);
      if (h.t === 'n') return '(' + x + '.t === "n" && ' + x + '.v === ' + numLit(h.v) + ' && ' + x + '.f === ' + !!h.f + ')';
      if (h.t === 's') return '(' + x + '.t === "s" && ' + x + '.v === ' + JSON.stringify(h.v) + ')';
      return '(' + x + '.t === "c" && ' + x + '.f === ' + JSON.stringify(h.f) + ' && ' + x + '.a.length === ' + h.a.length + ')';
    }
    function numLit(v) { return Number.isFinite(v) ? String(v) : (v > 0 ? 'Infinity' : v < 0 ? '-Infinity' : 'NaN'); }
    // a clause: inline (single-clause predicate: head failure returns false) or fn (head failure returns undefined)
    function genClause(cl, ci, A) {
      const vars = termVars(Cmp('-', [cl.head, cl.body]));
      const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
      const decl = vars.length ? 'let ' + vars.map((_, i) => 'v' + i).join(', ') + ';\n' : '';
      const seen = new Set();
      const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
      const mk = (headFail) => {
        seen.clear(); let d = 0;
        const match = (h, x) => {
          h = D(h);
          if (h.t === 'v') { const i = slot.get(h); if (!seen.has(h)) { seen.add(h); return 'v' + i + ' = ' + x + ';\n'; } return 'if (!E.unify(v' + i + ', ' + x + ')) ' + headFail + '\n'; }
          const t = 'h' + (d++);
          if (h.t !== 'c') return '{ const ' + t + ' = D(' + x + '); if (' + t + '.t === "v") E.bind(' + t + ', ' + K(h) + '); else if (!(' + keyTest(h, t) + ')) ' + headFail + ' }\n';
          // the build branch creates the pattern's new variables lazily, the match branch assigns them:
          // either way they are defined afterwards, so first occurrences are tracked once, in order
          const b = build(h, slot);
          let sub = '';
          h.a.forEach((y, i) => { sub += match(y, t + '.a[' + i + ']'); });
          return '{ const ' + t + ' = D(' + x + ');\nif (' + t + '.t === "v") E.bind(' + t + ', ' + b + ');\nelse if (' + t + '.t === "c" && ' + t + '.f === ' + JSON.stringify(h.f) + ' && ' + t + '.a.length === ' + h.a.length + ') {\n' + sub + '} else ' + headFail + ' }\n';
        };
        let code = '';
        hargs.forEach((h, i) => { code += match(h, A[i]); });
        return code;
      };
      const bodyCode = (fail) => { mentioned = new Set(termVars(cl.head)); return goal(cl.body, slot, fail); };
      const inlineHead = mk('{ E.undo(m0); return false; }');
      const inl = decl + 'const m0 = E.trail.length;\n' + inlineHead + bodyCode('return false;') + 'return true;';
      const fnHead = mk('{ E.undo(m0); return undefined; }');
      const fn = decl + 'const m0 = E.trail.length;\n' + fnHead + bodyCode('return false;') + 'return true;';
      return { inline: inl, fn };
    }
    function build(t, slot) {
      t = D(t);
      if (t.t === 'v') { const i = slot.get(t); return '(v' + i + ' || (v' + i + ' = V(' + JSON.stringify(t.name) + ')))'; }
      if (t.t !== 'c' || P.isGround(t)) { if (t.t === 'c') markGround(t); return K(t); }
      return '{t: "c", f: ' + JSON.stringify(t.f) + ', a: [' + t.a.map(x => build(x, slot)).join(', ') + ']}';
    }
    const mention = t => { for (const v of termVars(t)) mentioned.add(v); };
    const ARITH2 = { '+': '+', '-': '-', '*': '*' };
    const CMP = { '=:=/2': '===', '=\\=/2': '!==', '</2': '<', '>/2': '>', '=</2': '<=', '>=/2': '>=' };
    // an integer expression compiled to JS: leaves are integers or variables, operators + - * and unary -;
    // a leaf that is not an integer sets bad, and the generic builtin runs instead (errors, floats)
    function arith(t, slot) {
      t = D(t);
      if (t.t === 'n') return t.f || !Number.isSafeInteger(t.v) ? null : '(' + t.v + ')';
      if (t.t === 'v') { const i = slot.get(t); return '((q = D(v' + i + ' || BADV)).t === "n" && !q.f ? q.v : (bad = true, 0))'; }
      if (t.t !== 'c') return null;
      if (t.a.length === 2 && ARITH2[t.f]) { const a = arith(t.a[0], slot), b = arith(t.a[1], slot); return a && b ? '(' + a + ' ' + ARITH2[t.f] + ' ' + b + ')' : null; }
      if (t.a.length === 1 && t.f === '-') { const a = arith(t.a[0], slot); return a ? '(-' + a + ')' : null; }
      return null;
    }
    function goal(g, slot, FAIL) {
      const code = goal0(g, slot, FAIL); mention(g); return code;
    }
    // builtin_rows(member(X, L), P), splice_extend(P, [member(X, L)], Env, R), with P used nowhere else:
    // for each element Y of the proper list L, unify X = Y in place, copy Env, undo.  This is what the two goals
    // compute (each row is the goal's instance; unifying it back binds X and nothing else that is observable).
    function fuseGen(g1, g2, rest, slot, FAIL) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4') return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]);
      const gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || P.show(pat[0]) !== P.show(G) || !sameTerm(pat[0], G)) return null;
      if (rest.some(x => termVars(x).includes(Pv)) || termVars(g2.a[2]).includes(Pv) || termVars(g2.a[3]).includes(Pv) || mentioned.has(Pv)) return null;
      const generic = goal0(g1, slot, FAIL) + goal0(g2, slot, FAIL);
      if (gk === 'permutation/2') {
        // permutation(Xs, Ys) with Xs a proper list: the builtin's order (each element first in turn, then the
        // permutations of the rest), each permutation unified with Ys, the environment copied, undone
        return '{ const xs = LA(' + build(G.a[0], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' + TICK + ' ' + TICK + '\nconst y = ' + build(G.a[1], slot) + ', env = ' + build(g2.a[2], slot) + ', res = [];\n' +
          'PERMS(xs, p => { const m = E.trail.length; if (E.unify(y, p)) { E.steps += 2; if (E.steps > E.stepLimit) OVER(E); res.push(COPY(env)); if (res.length > 1e6) throw new LIMIT("builtin_rows: infinite generator permutation/2 (no finite packet)"); } E.undo(m); });\n' +
          'E.rowsBuilt += res.length; if (res.length > E.maxRows) E.maxRows = res.length;\n' +
          '{ const m = E.trail.length; if (!E.unify(' + build(g2.a[3], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
      }
      // steps as the two goals count them: one per call and one per solution, for each of the two
      return '{ const xs = LA(' + build(G.a[1], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[0], slot) + ', env = ' + build(g2.a[2], slot) + ', res = [];\n' +
        'for (let i = 0; i < xs.length; i++) { const m = E.trail.length; if (E.unify(x, xs[i])) { E.steps += 2; if (E.steps > E.stepLimit) OVER(E); res.push(COPY(env)); } E.undo(m); }\n' +
        'E.rowsBuilt += res.length; if (res.length > E.maxRows) E.maxRows = res.length;\n' +
        '{ const m = E.trail.length; if (!E.unify(' + build(g2.a[3], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
    }
    // generator, splice and row loop in one loop:
    //   builtin_rows(G, P), splice_extend(P, [G], e(Env), R2), loop(R2, R1)
    // with G member/2 or permutation/2 over a proper list, loop a packet loop (no cut) whose row predicate
    // starts by copying its row: each solution is bound in place, the row predicate runs on the environment
    // directly (it copies it first), its rows are copied (they may hold variables bound inside the row
    // predicate) and kept, and the binding is undone.  Same rows in the same order,
    // with the steps the three goals count; the list of rows R2 is never built.
    function fuseGenLoop(g1, g2, g3, rest, slot, FAIL) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4') return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]), gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || !sameTerm(pat[0], G)) return null;
      const R2 = D(g2.a[3]); if (R2.t !== 'v' || D(g3.a ? g3.a[0] : null) !== R2 || !g3.a || g3.a.length !== 2) return null;
      const k3 = P.key(g3); const lcls = prog.preds.get(k3); if (!lcls) return null;
      const sh = loopShape(k3, lcls); if (!sh || sh.cutVariant || !fname.has(sh.callKey)) return null;
      // the row predicate's row clause must copy its row before anything else
      const rcl = (prog.preds.get(sh.callKey) || []).find(c => isC(D(c.head).a[0], 'e', 1));
      if (!rcl || P.key(D(P.flatConj(rcl.body)[0])) !== 'copy_term/2' || D(D(P.flatConj(rcl.body)[0]).a[0]) !== D(D(D(rcl.head).a[0]).a[0])) return null;
      const used = rest.concat([g3.a[1]]).some(x => termVars(x).some(v => v === Pv || v === R2)) || termVars(g2.a[2]).includes(R2) || mentioned.has(Pv) || mentioned.has(R2);
      if (used) return null;
      const env = g2.a[2]; if (!isC(env, 'e', 1)) return null;
      const generic = goal0(g1, slot, FAIL) + goal0(g2, slot, FAIL) + goal0(g3, slot, FAIL);
      const rf = fname.get(sh.callKey);
      // a DET filter as the row predicate:
      //   r(e(W), O) :- copy_term(W, L), if_commit((q__d(As.., S), S \== maybe), if_commit(S = yes, O = [e(L)], O = []), Packet)
      // the native q__d runs on the solution in place; only a kept row is copied.  Without a native function
      // (or when it declines) the row predicate runs as above.
      let filt = null;
      { const rb = P.flatConj(rcl.body).map(D);
        const Lr = P.listToArray(rb[0].a[1]), Ev = P.listToArray(D(env).a[0]);
        const ic = rb[1];
        if (rb.length === 2 && Lr && Ev && Lr.length === Ev.length && Lr.every(v => D(v).t === 'v') && P.key(ic) === 'if_commit/3') {
          const c = P.flatConj(ic.a[0]).map(D), th = D(ic.a[1]);
          if (c.length === 2 && c[0].t === 'c' && /__d$/.test(c[0].f) && P.key(c[1]) === '\\==/2' && D(c[1].a[0]) === D(c[0].a[c[0].a.length - 1]) && P.key(th) === 'if_commit/3') {
            const Sv = D(c[0].a[c[0].a.length - 1]);
            const yes = D(th.a[0]), keep = D(th.a[1]), drop = D(th.a[2]);
            const Orow = D(D(rcl.head).a[1]);
            const okYes = P.key(yes) === '=/2' && D(yes.a[0]) === Sv && D(yes.a[1]).t === 'a' && D(yes.a[1]).n === 'yes';
            const okKeep = P.key(keep) === '=/2' && D(keep.a[0]) === Orow && sameTerm(keep.a[1], P.list([P.Cmp('e', [P.list(Lr)])]));
            const okDrop = P.key(drop) === '=/2' && D(drop.a[0]) === Orow && D(drop.a[1]).t === 'a' && D(drop.a[1]).n === '[]';
            // the call's arguments, over the loop's environment instead of the row's copy
            const sub = new Map(Lr.map((v, i) => [D(v), Ev[i]]));
            const subst = t => { t = D(t); if (t.t === 'v') return sub.has(t) ? sub.get(t) : null; if (t.t === 'c') { const a = t.a.map(subst); return a.includes(null) ? null : P.Cmp(t.f, a); } return t; };
            const args = c[0].a.slice(0, -1).map(subst);
            if (okYes && okKeep && okDrop && !args.includes(null)) filt = { k: P.key(c[0]), args };
          }
        } }
      if (filt) {
        const each = gk === 'member/2' ? '(fn) => { for (let i = 0; i < xs.length; i++) fn(xs[i]); }' : '(fn) => PERMS(xs, fn)';
        const argsCode = filt.args.map(a => build(a, slot)).join(', ');
        return '{ const xs = LA(' + build(G.a[1 - (gk === 'member/2' ? 0 : 1)], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' +
          TICK + ' ' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[gk === 'member/2' ? 0 : 1], slot) + ', ev = ' + build(env, slot) + ', res = []; let ok = true, nrow = 0;\n' +
          '(' + each + ')(y => { if (!ok) return; const m = E.trail.length; if (E.unify(x, y)) { E.steps += 4; if (E.steps > E.stepLimit) OVER(E); if (++nrow > 1e6) throw new LIMIT("builtin_rows: infinite generator ' + gk + ' (no finite packet)"); ' +
          'const Sv = V(null); const h = NATE(' + JSON.stringify(filt.k) + ', [' + argsCode + (argsCode ? ', ' : '') + 'Sv], E);\n' +
          'if (h === true) { E.steps += 1; if (D(Sv).n === "yes") res.push(COPY(ev)); }\n' +
          'else { const Ov = V(null); if (!' + rf + '(ev, Ov, E)) ok = false; else { const o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E); for (let j = 0; j < o1.length; j++) res.push(COPY(o1[j])); } } } E.undo(m); });\n' +
          'E.rowsBuilt += nrow; if (nrow > E.maxRows) E.maxRows = nrow;\n' +
          'if (!ok) { ' + FAIL + ' }\n{ const m = E.trail.length; if (!E.unify(' + build(g3.a[1], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
      }
      const each = gk === 'member/2'
        ? '(fn) => { for (let i = 0; i < xs.length; i++) fn(xs[i]); }'
        : '(fn) => PERMS(xs, fn)';
      return '{ const xs = LA(' + build(G.a[1 - (gk === 'member/2' ? 0 : 1)], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' +
        TICK + ' ' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[gk === 'member/2' ? 0 : 1], slot) + ', ev = ' + build(env, slot) + ', res = []; let ok = true, nrow = 0;\n' +
        '(' + each + ')(y => { if (!ok) return; const m = E.trail.length; if (E.unify(x, y)) { E.steps += 4; if (E.steps > E.stepLimit) OVER(E); if (++nrow > 1e6) throw new LIMIT("builtin_rows: infinite generator ' + gk + ' (no finite packet)"); const Ov = V(null); if (!' + rf + '(ev, Ov, E)) ok = false; else { const o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E); for (let j = 0; j < o1.length; j++) res.push(COPY(o1[j])); } } E.undo(m); });\n' +
        'E.rowsBuilt += nrow; if (nrow > E.maxRows) E.maxRows = nrow;\n' +
        'if (!ok) { ' + FAIL + ' }\n{ const m = E.trail.length; if (!E.unify(' + build(g3.a[1], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
    }
    function isC(t, f, n) { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; }
    function sameTerm(a, b) { a = D(a); b = D(b); if (a === b) return true; if (a.t !== b.t) return false; if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => sameTerm(x, b.a[i])); if (a.t === 'a') return a === b; if (a.t === 'n') return a.v === b.v && a.f === b.f; if (a.t === 's') return a.v === b.v; return false; }
    function goal0(g, slot, FAIL) {
      g = D(g); const k = P.key(g);
      if (k === 'is/2' || CMP[k]) {
        const rb = RBf(k);
        const generic = '{ const m = E.trail.length; if (!' + rb + '([' + g.a.map(x => build(x, slot)).join(', ') + '], E)) { E.undo(m); ' + FAIL + ' } }';
        if (k === 'is/2') {
          const ex = arith(g.a[1], slot);
          if (ex) return TICK + '\n{ let bad = false, q; const r = ' + ex + ';\nif (bad) ' + generic + '\nelse { const m = E.trail.length; if (!E.unify(' + build(g.a[0], slot) + ', INT(r))) { E.undo(m); ' + FAIL + ' } } }\n';
        } else {
          const ea = arith(g.a[0], slot), eb = arith(g.a[1], slot);
          if (ea && eb) return TICK + '\n{ let bad = false, q; const x = ' + ea + ', y = ' + eb + ';\nif (bad) ' + generic + '\nelse if (!(x ' + CMP[k] + ' y)) ' + FAIL + ' }\n';
        }
      }
      if (k === 'copy_term/2') {
        // copy_term(Ts, [V1..Vn]) with V1..Vn distinct variables not seen before: assign the copies
        const dst = P.listToArray(g.a[1]), src = P.listToArray(g.a[0]);
        const fresh = dst && dst.every((v, i) => { v = D(v); return v.t === 'v' && !mentioned.has(v) && dst.findIndex(w => D(w) === v) === i; }) && !termVars(g.a[0]).some(v => dst.some(w => D(w) === v));
        if (fresh && src && dst.length === src.length) {
          return TICK + '\n{ const mp = new Map(); ' + dst.map((v, i) => 'v' + slot.get(D(v)) + ' = COPY(' + build(src[i], slot) + ', mp);').join(' ') + ' }\n';
        }
        // copy_term(Row, [V1..Vn]): copy the row once; a proper list of n items is assigned, anything else unifies
        if (fresh && !src) {
          const rb = RBf(k);
          return TICK + '\n{ const c = COPY(' + build(g.a[0], slot) + '); const ca = LA(c);\nif (ca && ca.length === ' + dst.length + ') { ' + dst.map((v, i) => 'v' + slot.get(D(v)) + ' = ca[' + i + '];').join(' ') + ' }\nelse { const m = E.trail.length; if (!E.unify(c, ' + build(g.a[1], slot) + ')) { E.undo(m); ' + FAIL + ' } } }\n';
        }
      }
      if (k === ',/2') {
        const gs = P.flatConj(g).map(D); let code = '';
        for (let i = 0; i < gs.length; i++) {
          const f3 = i + 2 < gs.length && fuseGenLoop(gs[i], gs[i + 1], gs[i + 2], gs.slice(i + 3), slot, FAIL);
          if (f3) { code += f3; mention(gs[i]); mention(gs[i + 1]); mention(gs[i + 2]); i += 2; continue; }
          const f = i + 1 < gs.length && fuseGen(gs[i], gs[i + 1], gs.slice(i + 2), slot, FAIL);
          if (f) { code += f; mention(gs[i]); mention(gs[i + 1]); i++; continue; }
          code += goal(gs[i], slot, FAIL);
        }
        return code;
      }
      if (k === 'true/0') return TICK + '\n';
      if (k === 'fail/0' || k === 'false/0') return TICK + ' ' + FAIL + '\n';
      if (k === 'if_commit/3') {
        const L = 'L' + (lab++);
        return TICK + ' E.decisions++;\n{ const m' + L + ' = E.trail.length; let ok' + L + ' = false;\n' + L + ': {\n' + goal(g.a[0], slot, 'break ' + L + ';') + 'ok' + L + ' = true;\n}\nif (ok' + L + ') {\n' + goal(g.a[1], slot, FAIL) + '} else {\nE.undo(m' + L + ');\n' + goal(g.a[2], slot, FAIL) + '}\n}\n';
      }
      if (k === '=/2') return TICK + '\n{ const m = E.trail.length; if (!E.unify(' + build(g.a[0], slot) + ', ' + build(g.a[1], slot) + ')) { E.undo(m); ' + FAIL + ' } }\n';
      const as = g.t === 'c' ? g.a.map(x => build(x, slot)) : [];
      if (prog.preds.has(k)) {
        if (/__d$/.test(g.f) && !/__d$/.test(curPred)) return '{ const h = NATE(' + JSON.stringify(k) + ', [' + as.join(', ') + '], E); if (h === undefined && !' + fname.get(k) + '(' + as.concat(['E']).join(', ') + ')) ' + FAIL + ' }\n';
        return 'if (!' + fname.get(k) + '(' + as.concat(['E']).join(', ') + ')) ' + FAIL + '\n';
      }
      const rb = RBf(k);
      if (rb) return TICK + '\n{ const m = E.trail.length; if (!' + rb + '([' + as.join(', ') + '], E)) { E.undo(m); ' + FAIL + ' } }\n';
      return 'throw new Error(' + JSON.stringify('Detlog engine: unknown procedure ' + k) + ');\n';
    }
    let curPred = '';
    for (const [k, cls] of prog.preds) {
      curPred = k.slice(0, k.lastIndexOf('/'));
      const n = arityOf(k), A = []; for (let i = 0; i < n; i++) A.push('a' + i);
      const sig = A.concat(['E']).join(', ');
      const sh = loopShape(k, cls);
      if (sh && fname.has(sh.callKey)) {
        const cf = fname.get(sh.callKey);
        out.push('function ' + fname.get(k) + '(' + sig + ') {\n' + TICK +
          '\nconst items = LA(a0); if (!items) return false; const res = [];\nfor (let i = 0; i < items.length; i++) {\nE.steps += 2; if (E.steps > E.stepLimit) OVER(E);\nconst Ov = V(null);\nif (!' + cf + '(items[i], Ov, E)) return false;\nconst o1 = LA(Ov); E.steps += (o1.length || 1); if (E.steps > E.stepLimit) OVER(E);\n' +
          (sh.cutVariant ? 'let hc = false; for (const x of o1) { res.push(x); const xd = D(x); if (xd.t === "a" && xd.n === "cut") hc = true; }\nif (hc) { const it = D(items[i]); if (it.t === "c" && it.f === "e") break; }\n' : 'for (let j = 0; j < o1.length; j++) res.push(o1[j]);\n') +
          '}\nreturn E.unify(a1, LIST(res));\n}');
        continue;
      }
      const clauseFns = cls.map((cl, ci) => genClause(cl, ci, A));
      const nm = fname.get(k);
      if (cls.length === 1) { out.push('function ' + nm + '(' + sig + ') {\n' + TICK + '\n' + clauseFns[0].inline + '\n}'); continue; }
      // clause selection by first argument, as in compilePred: variable -> all clauses; otherwise the clauses
      // whose first head argument is a variable or has the argument's key, in order
      clauseFns.forEach((c, i) => out.push('function ' + nm + '_' + i + '(' + sig + ') {\n' + c.fn + '\n}'));
      const calls = i => '{ const r = ' + nm + '_' + i + '(' + sig + '); if (r !== undefined) return r; }';
      let body = TICK + '\n';
      if (!n || cls.length === 0) body += cls.map((_, i) => calls(i)).join('\n') + '\nreturn false;';
      else {
        const tests = cls.map(cl => keyTest(D(D(cl.head).a[0]), 't0'));
        body += 'const t0 = D(a0);\nif (t0.t === "v") {\nif (E.violations.length < 1000) E.violations.push(' + JSON.stringify(k) + ');\n' + cls.map((_, i) => calls(i)).join('\n') + '\nreturn false;\n}\n';
        body += tests.map((t, i) => 'const k' + i + ' = ' + t + ';').join('\n') + '\n';
        body += 'if ((' + tests.map((_, i) => '(k' + i + ' ? 1 : 0)').join(' + ') + ') > 1 && E.violations.length < 1000) E.violations.push(' + JSON.stringify(k) + ');\n';
        body += cls.map((_, i) => 'if (k' + i + ') ' + calls(i)).join('\n') + '\nreturn false;';
      }
      out.push('function ' + nm + '(' + sig + ') {\n' + body + '\n}');
    }
    // ---------------- native tier: DET predicates in functional mode ----------------
    // A deterministic-mode predicate p__d(X1..Xn, S) entered from packet code with ground inputs ('i') and
    // fresh, distinct output variables ('o') is compiled, for that mode, to a JS function of its inputs that
    // returns its outputs (or NO / MAYBE): ground terms in and out, no logic variables, no trail, native
    // integer arithmetic, direct calls between native functions.  Anything the analysis cannot follow means
    // "no native function for this mode"; anything unexpected at run time (a non-integer in arithmetic, a
    // zero divisor, a deep stack) throws BAIL and the generic p__d runs from the untouched arguments, so
    // answers and errors are the generic code's.  Pure code: running it twice cannot be observed.
    const NAT = { fns: Object.create(null), done: new Map(), seq: 0, entry: new Map() };
    // the JavaScript emitter for the shared native compiler (src/native.js)
    const EMJS = {
      YES: 'H.YES', NO: 'H.NO', MAYBE: 'H.MAYBE', EQOP: '===', NEOP: '!==', BAIL: 'throw H.BAIL;',
      v: name => name,
      num: v => String(v),
      k: t => { if (t.t === 'c') markGround(t); return K(t); },
      box: e => 'H.INT(' + e + ')',
      unbox: e => 'H.IV(' + e + ')',
      cmp: (f, args) => '{t: "c", f: ' + JSON.stringify(f) + ', a: [' + args.join(', ') + '], gr: true}',
      eq: (a, b) => 'H.EQ(' + a + ', ' + b + ')',
      isIntVal: (e, v) => 'H.ISV(' + e + ', ' + v + ')',
      tmp: (t, e) => 'const ' + t + ' = ' + e + ';',
      isCmp: (t, f, n) => t + '.t === "c" && ' + t + '.f === ' + JSON.stringify(f) + ' && ' + t + '.a.length === ' + n,
      arg: (t, i) => t + '.a[' + i + ']',
      keyTest: (pat, t) => pat.t === 'a' ? t + ' === ' + K(pat) : keyTest(pat, t),
      fn: (name, args) => name === 'MIN' ? 'Math.min(' + args.join(', ') + ')' : name === 'MAX' ? 'Math.max(' + args.join(', ') + ')' : name === 'ABS' ? 'Math.abs(' + args[0] + ')' : 'H.' + name + '(' + args.join(', ') + ')',
      assign: (lhs, rhs) => lhs + ' = ' + rhs + ';\n',
      fail: L => 'break ' + L + ';',
      blockNoThen: (L, rc, re) => L + ': {\n' + rc + '}\n' + re,
      block: (L, ok, rc, rt, re) => '{ let ' + ok + ' = false;\n' + L + ': {\n' + rc + ok + ' = true;\n}\nif (' + ok + ') {\n' + rt + '} else {\n' + re + '}\n}\n',
      retOuts: vals => vals.length === 1 ? 'return ' + vals[0] + ';' : vals.map((v, i) => 'H.OUTS[' + i + '] = ' + v + ';').join(' ') + ' return H.YES;',
      retStatus: v => 'return ' + v + ';',
      call: (callee, ins, outs, retInt, rs, memo) => {
        const assign = outs.length === 1 ? outs[0] + ' = r;' : outs.map((o, i) => o + ' = H.OUTS[' + i + '];').join(' ');
        const get = memo
          ? 'const kk = H.KEY(' + ins.join(', ') + '); const T = H.TAB(' + JSON.stringify(memo.table) + '); let r = T.get(kk); if (r === undefined) { r = ' + callee + '(' + ins.join(', ') + '); T.set(kk, r); }\n'
          : 'const r = ' + callee + '(' + ins.join(', ') + ');\n';
        return '{ ' + get + 'if (r === H.NO || r === H.MAYBE) ' + rs + ' = r; else { ' + assign + ' ' + rs + ' = H.YES; } }\n';
      },
      func: (name, params, nOuts, selfInt, used, statusLocals, body) => {
        const names = [...new Set(used.map(u => u.name))];
        return 'function ' + name + '(' + params.map(p => p.name).join(', ') + ') {\nif (++H.N.s > H.N.l) H.OVER();\n' +
          (names.length ? 'let ' + names.join(', ') + ';\n' : '') + (statusLocals.length ? 'let ' + statusLocals.join(', ') + ';\n' : '') + body + 'throw H.BAIL;\n}';
      },
    };
    function nativeFor(k, mode) {
      const key = k + '|' + mode;
      if (NAT.done.has(key)) return NAT.done.get(key);
      const doneView = { has: k2 => NAT.done.has(k2), get: k2 => { const f = NAT.done.get(k2); return f ? { ref: 'NF.' + f.nativeName, retInt: f.retInt } : null; } };
      const batch = P.nativeBatch(prog, k, mode, EMJS, doneView, () => 'n' + (NAT.seq++));
      if (!batch) { NAT.done.set(key, null); return null; }
      const names = [...batch.values()].map(e => e.name);
      const src = '"use strict";\n' + [...batch.values()].map(e => e.src).join('\n') + '\nreturn {' + names.map(n => n + ': ' + n).join(', ') + '};';
      const made = new Function('K', 'NF', 'H', src)(consts, NAT.fns, NH);
      for (const [key2, e] of batch) { const f = made[e.name]; f.nativeName = e.name; f.retInt = e.retInt; NAT.fns[e.name] = f; NAT.done.set(key2, f); }
      return NAT.done.get(key);
    }
    // run-time entry from packet code: decide the mode, run the native function, bind the outputs
    const NH = {
      YES: { native: 'yes' }, NO: { native: 'no' }, MAYBE: { native: 'maybe' }, BAIL: { native: 'bail' }, OUTS: [], N: { s: 0, l: 0 },
      IV: x => (x.t === 'n' && !x.f) ? x.v : bailN(),
      IDIV: (a, b) => b === 0 ? bailN() : Math.trunc(a / b),
      IMOD: (a, b) => { if (b === 0) return bailN(); const m = a % b; return m !== 0 && (m < 0) !== (b < 0) ? m + b : m; },
      IREM: (a, b) => b === 0 ? bailN() : a % b,
      INT: v => ({ t: 'n', v, f: false }),
      ISV: (x, v) => x.t === 'n' && !x.f && x.v === v,
      EQ: eqG, OVER: () => { throw new P.LimitError('step limit exceeded'); },
      // tables for memoised native calls: one per callee and mode, emptied at each entry from packet code
      T: new Map(),
      TAB: k => { let t = NH.T.get(k); if (!t) { t = new Map(); NH.T.set(k, t); } return t; },
      KEY: function () { if (arguments.length === 1) { const x = arguments[0]; if (typeof x === 'number') return x; if (x.t === 'n' && !x.f) return x.v; } let s = ''; for (let i = 0; i < arguments.length; i++) { const x = arguments[i]; s += (typeof x === 'number' ? 'i' + x : P.variantKey(x)) + '\u0001'; } return s; },
    };
    function bailN() { throw NH.BAIL; }
    // every permutation of xs, as a list, in permutation/2's order; ground lists are marked ground
    function perms(xs, fn) {
      const n = xs.length, ground = xs.every(x => { x = D(x); return x.t !== 'v' && (x.t !== 'c' || x.gr === true); });
      const cur = new Array(n), used = new Array(n).fill(false);
      const xr = xs.map(D);
      (function rec(k) {
        if (k === n) { let l = P.NIL; for (let i = n - 1; i >= 0; i--) l = ground ? { t: 'c', f: '.', a: [cur[i], l], gr: true } : { t: 'c', f: '.', a: [cur[i], l] }; fn(l); return; }
        // the builtin removes the chosen element and permutes the rest in their original order
        for (let i = 0; i < n; i++) if (!used[i]) { used[i] = true; cur[k] = xr[i]; rec(k + 1); used[i] = false; }
      })(0);
    }
    function eqG(a, b) {
      if (a === b) return true;
      if (a.t !== b.t) return false;
      if (a.t === 'n') return a.v === b.v && a.f === b.f;
      if (a.t === 's') return a.v === b.v;
      if (a.t !== 'c' || a.f !== b.f || a.a.length !== b.a.length) return false;
      for (let i = 0; i < a.a.length; i++) if (!eqG(a.a[i], b.a[i])) return false;
      return true;
    }
    const ATOMS = { yes: P.Atom('yes'), no: P.Atom('no') };
    // returns true when the native function answered (outputs and status bound), undefined otherwise
    function natEntry(k, args, E) {
      if (!P.DETLOG_NATIVE) return undefined;
      const n = args.length - 1; let mode = ''; const ins = [], outv = [];
      for (let i = 0; i < n; i++) {
        const x = D(args[i]);
        if (x.t === 'v') { if (outv.includes(x)) return undefined; mode += 'o'; outv.push(x); continue; }
        if (x.t === 'n' && !x.f) { mode += 'n'; ins.push(x.v); continue; }
        const r = P.resolve(x);
        if (r.t === 'c' && !r.gr) return undefined;
        mode += 'i'; ins.push(r);
      }
      const S = D(args[n]); if (S.t !== 'v' || outv.includes(S)) return undefined;
      // per predicate: mode -> native function (or null), without building a key per call
      let byMode = NAT.entry.get(k); if (!byMode) { byMode = new Map(); NAT.entry.set(k, byMode); }
      let fn = byMode.get(mode); if (fn === undefined) { fn = nativeFor(k, mode); byMode.set(mode, fn); }
      if (!fn) return undefined;
      let r;
      NH.N.s = E.steps; NH.N.l = E.stepLimit; if (NH.T.size) NH.T.clear();
      try { r = fn.apply(null, ins); }
      catch (e) { E.steps = NH.N.s; if (e === NH.BAIL || e instanceof RangeError) return undefined; throw e; }
      E.steps = NH.N.s; E.nativeCalls = (E.nativeCalls || 0) + 1;
      if (r === NH.MAYBE) return undefined;
      if (r === NH.NO) { E.bind(S, ATOMS.no); return true; }
      if (outv.length === 1) E.bind(outv[0], fn.retInt ? P.Int(r) : r); else for (let i = 0; i < outv.length; i++) E.bind(outv[i], NH.OUTS[i]);
      E.bind(S, ATOMS.yes); return true;
    }
    P.nativeFor = nativeFor;

    const src = '"use strict";\n' + out.join('\n') + '\nreturn {' + [...fname].map(([k, f]) => JSON.stringify(k) + ': ' + f).join(', ') + '};';
    const OVER = E => { throw new P.LimitError('step limit (' + E.stepLimit + ') exceeded'); };
    const BADV = { t: 'v', ref: null }; // stands for a variable that was never created (an unbound leaf)
    const fns = new Function('K', 'RB', 'D', 'V', 'LA', 'LIST', 'OVER', 'INT', 'COPY', 'BADV', 'NATE', 'PERMS', 'LIMIT', src)(consts, rbs, D, Var, listToArray, list, OVER, P.Int, P.copy, BADV, natEntry, perms, P.LimitError);
    const preds = new Map();
    for (const [k, f] of Object.entries(fns)) preds.set(k, { k, fn: (args, E) => f(...args, E), pos: f });
    return { preds, src, jit: true, nat: NAT };
  }

  const cache = new WeakMap();
  function compiled(prog) {
    let f = cache.get(prog);
    if (!f) {
      try { f = P.DETLOG_JIT === false ? new FastDetlog(prog) : jitCompile(prog); }
      catch (e) { f = new FastDetlog(prog); f.jitError = e.message; }
      cache.set(prog, f);
    }
    return f;
  }
  P.jitCompile = jitCompile;
  P.loopShape = loopShape;
  // the (predicate, mode) pairs the native tier compiled for a program (the C export compiles the same)
  P.nativeModesOf = prog => { const F = cache.get(prog); return F && F.nat ? [...F.nat.done].filter(([, f]) => f).map(([k]) => k) : []; };
  if (P.DETLOG_NATIVE === undefined) P.DETLOG_NATIVE = true;

  // same interface and result shape as runDetlog
  function runDetlogFast(prog, qpred, varNames, opts) {
    opts = opts || {};
    let F;
    try { F = compiled(prog); } catch (e) { return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (compile failed: ' + e.message + ')' }); }
    const E = new P.DetEngine(prog, opts);
    const nv = varNames.length, args = new Array(nv + 1);
    for (let i = 0; i < nv; i++) args[i] = Var(varNames[i]);
    const Rv = Var('R'); args[nv] = Rv;
    const k = qpred + '__cp/' + (nv + 1);
    const t0 = P.now(); let ok = false, error = null;
    try {
      const r = F.preds.get(k); if (!r || !r.fn) throw new Error('no query predicate ' + k);
      ok = r.pos ? (args.push(E), r.pos.apply(null, args)) : r.fn(args, E);
    } catch (e) {
      if (e instanceof RangeError) return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (JS stack exhausted)' });
      error = e.message;
    }
    const t1 = P.now();
    const res = P.decodePacket(ok, error, Rv, varNames);
    return { ok: res.ok, answers: res.answers, events: res.events, output: res.output, error: res.error,
      engine: F.jit ? 'fast (JIT)' : 'fast', steps: E.steps, decisions: E.decisions, violations: E.violations.length,
      violationPreds: E.violations.length ? [...new Set(E.violations)] : [], cps: 0, maxCP: 0, timeMs: t1 - t0,
      memoHits: E.memoHits, memoStores: E.memoStores, rowsBuilt: E.rowsBuilt, maxRows: E.maxRows };
  }
  P.FastDetlog = FastDetlog; P.runDetlogFast = runDetlogFast;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
