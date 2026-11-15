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
      if (P.key(G) !== 'member/2' || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || P.show(pat[0]) !== P.show(G) || !sameTerm(pat[0], G)) return null;
      if (rest.some(x => termVars(x).includes(Pv)) || termVars(g2.a[2]).includes(Pv) || termVars(g2.a[3]).includes(Pv) || mentioned.has(Pv)) return null;
      const generic = goal0(g1, slot, FAIL) + goal0(g2, slot, FAIL);
      // steps as the two goals count them: one per call and one per solution, for each of the two
      return '{ const xs = LA(' + build(G.a[1], slot) + ');\nif (xs === null) {\n' + generic + '} else {\n' + TICK + ' ' + TICK + '\nconst x = ' + build(G.a[0], slot) + ', env = ' + build(g2.a[2], slot) + ', res = [];\n' +
        'for (let i = 0; i < xs.length; i++) { const m = E.trail.length; if (E.unify(x, xs[i])) { E.steps += 2; if (E.steps > E.stepLimit) OVER(E); res.push(COPY(env)); } E.undo(m); }\n' +
        'E.rowsBuilt += res.length; if (res.length > E.maxRows) E.maxRows = res.length;\n' +
        '{ const m = E.trail.length; if (!E.unify(' + build(g2.a[3], slot) + ', LIST(res))) { E.undo(m); ' + FAIL + ' } } } }\n';
    }
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
      if (prog.preds.has(k)) return 'if (!' + fname.get(k) + '(' + as.concat(['E']).join(', ') + ')) ' + FAIL + '\n';
      const rb = RBf(k);
      if (rb) return TICK + '\n{ const m = E.trail.length; if (!' + rb + '([' + as.join(', ') + '], E)) { E.undo(m); ' + FAIL + ' } }\n';
      return 'throw new Error(' + JSON.stringify('Detlog engine: unknown procedure ' + k) + ');\n';
    }
    for (const [k, cls] of prog.preds) {
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
    const src = '"use strict";\n' + out.join('\n') + '\nreturn {' + [...fname].map(([k, f]) => JSON.stringify(k) + ': ' + f).join(', ') + '};';
    const OVER = E => { throw new P.LimitError('step limit (' + E.stepLimit + ') exceeded'); };
    const BADV = { t: 'v', ref: null }; // stands for a variable that was never created (an unbound leaf)
    const fns = new Function('K', 'RB', 'D', 'V', 'LA', 'LIST', 'OVER', 'INT', 'COPY', 'BADV', src)(consts, rbs, D, Var, listToArray, list, OVER, P.Int, P.copy, BADV);
    const preds = new Map();
    for (const [k, f] of Object.entries(fns)) preds.set(k, { k, fn: (args, E) => f(...args, E), pos: f });
    return { preds, src, jit: true };
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
