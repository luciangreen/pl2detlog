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
    const r = this.ref(P.key(call));
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

  const cache = new WeakMap();
  function compiled(prog) { let f = cache.get(prog); if (!f) { f = new FastDetlog(prog); cache.set(prog, f); } return f; }

  // same interface and result shape as runDetlog
  function runDetlogFast(prog, qpred, varNames, opts) {
    opts = opts || {};
    let F;
    try { F = compiled(prog); } catch (e) { return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (compile failed: ' + e.message + ')' }); }
    const E = new P.DetEngine(prog, opts);
    const vs = varNames.map(n => Var(n)); const Rv = Var('R');
    const k = qpred + '__cp/' + (varNames.length + 1);
    const t0 = P.now(); let ok = false, error = null;
    try {
      const r = F.preds.get(k); if (!r || !r.fn) throw new Error('no query predicate ' + k);
      ok = r.fn(vs.concat([Rv]), E);
    } catch (e) {
      if (e instanceof RangeError) return Object.assign(P.runDetlog(prog, qpred, varNames, opts), { engine: 'reference (JS stack exhausted)' });
      error = e.message;
    }
    const t1 = P.now();
    const res = P.decodePacket(ok, error, Rv, varNames);
    return Object.assign(res, { steps: E.steps, decisions: E.decisions, violations: E.violations.length, violationPreds: [...new Set(E.violations)], cps: 0, maxCP: 0, timeMs: t1 - t0, memoHits: E.memoHits, memoStores: E.memoStores, rowsBuilt: E.rowsBuilt, maxRows: E.maxRows, engine: 'fast' });
  }
  P.FastDetlog = FastDetlog; P.runDetlogFast = runDetlogFast;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
