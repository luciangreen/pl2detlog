/* pl2detlog Detlog interpreter: the choicepointless, cutless interpreter of detlog2 (part 1).
   It runs the cut-free program (rule CUT applied, higher-order calls specialised) as answer packets:
   - a predicate call computes the callee's packet (its answers and output, in Prolog order) and splices
     it into the conjunction: one row at a time, bindings undone between rows - no choicepoint is ever
     created, so there is no choicepoint stack and nothing to backtrack into;
   - clauses are compiled once into closures, and heads are matched WAM-style without copying;
   - commitment ((C -> T ; E), \+, once) takes the first row of C and never demands the rest;
   - a cut inside a branch (a cut marker in the converted code) is a status that stops the remaining
     rows and clauses of its clause's predicate.
   Its answers are checked against Prolog and against the converted Detlog code by the proof checker. */
(function (P) {
  'use strict';
  const { Var, Cmp, NIL, list, deref, listToArray, termVars, Int, Str, Atom } = P;
  const D = deref;
  const OK = 0, STOP = 1, CUT = 2;

  function Machine(opts) {
    opts = opts || {};
    this.trail = []; this.steps = 0; this.stepLimit = opts.stepLimit || 5e7; this.items = null; this.calls = 0; this.rows = 0; this.globals = new Map(); this.out = '';
  }
  Machine.prototype.bind = function (v, t) { v.ref = t; this.trail.push(v); };
  Machine.prototype.undo = function (m) { const tr = this.trail; while (tr.length > m) tr.pop().ref = null; };
  Machine.prototype.unify = P.Engine.prototype.unify;
  Machine.prototype.tick = function (n) { this.steps += n || 1; if (this.steps > this.stepLimit) throw new P.LimitError('step limit (' + this.stepLimit + ') exceeded'); };
  // output goes into the packet being built, in the order it is written
  Machine.prototype.write = function (s) { if (!s) return; const it = this.items; const l = it[it.length - 1]; if (l && l.out !== undefined) l.out += s; else it.push({ out: s }); };

  function Interp(conv) {
    this.ir = conv.ir; this.preds = new Map(); this.prog = conv.prog;
    for (const [k, p] of conv.ir) this.ref(k).p = p;
    for (const [k, p] of conv.ir) this.ref(k).fn = this.compilePred(k, p);
  }
  Interp.prototype.ref = function (k) { let r = this.preds.get(k); if (!r) { r = { k, fn: null }; this.preds.set(k, r); } return r; };

  // packet of k(args): array of {row: [instances of args]} and {out: text}
  Interp.prototype.compilePred = function (k, p) {
    if (p.error) return () => { throw new Error('not converted: ' + k + ': ' + p.error); };
    const cc = p.clauses.map(cl => this.compileClause(cl));
    const n = +k.slice(k.lastIndexOf('/') + 1);
    const keyOf = t => { t = D(t); return t.t === 'c' ? 'c' + t.f + '/' + t.a.length : t.t === 'a' ? 'a' + t.n : t.t === 'n' ? 'n' + t.v + (t.f ? 'f' : '') : t.t === 's' ? 's' + t.v : null; };
    const heads = p.clauses.map(cl => n ? keyOf(D(cl.head).a[0]) : null);
    const index = new Map(); const varIdx = [];
    heads.forEach((h, i) => { if (h === null) varIdx.push(i); });
    for (const h of new Set(heads.filter(x => x !== null))) index.set(h, heads.map((x, i) => (x === h || x === null) ? i : -1).filter(i => i >= 0));
    const all = cc.map((_, i) => i);
    return function (args, M) {
      M.tick(); M.calls++;
      let cand = all;
      if (n && cc.length > 1) { const a0 = D(args[0]); if (a0.t !== 'v') cand = index.get(keyOf(a0)) || varIdx; }
      const save = M.items; const items = []; M.items = items;
      try {
        for (let j = 0; j < cand.length; j++) {
          const c = cc[cand[j]];
          const env = new Array(c.nslots); const m = M.trail.length;
          let st = OK;
          if (c.head(args, env, M)) st = c.body(env, M, () => { const row = new Array(n); for (let i = 0; i < n; i++) row[i] = P.resolve(args[i]); items.push({ row }); M.rows++; return OK; });
          M.undo(m);
          if (st === CUT) break; // a cut stops the remaining clauses
        }
      } finally { M.items = save; }
      return items;
    };
  };
  Interp.prototype.compileClause = function (cl) {
    const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
    const vars = termVars(Cmp('-', [cl.head, cl.body]));
    const slot = new Map(); vars.forEach((v, i) => slot.set(v, i));
    const seen = new Set();
    const ms = hargs.map(h => P.FastDetlog.prototype.compileMatch.call(this, h, slot, seen));
    const nh = ms.length;
    return { nslots: vars.length, head: nh ? (args, env, M) => { for (let i = 0; i < nh; i++) if (!ms[i](args[i], env, M)) return false; return true; } : () => true, body: this.compileGoal(cl.body, slot) };
  };
  Interp.prototype.compileBuild = P.FastDetlog.prototype.compileBuild;
  Interp.prototype.compileMatch = P.FastDetlog.prototype.compileMatch;

  // a goal is compiled to g(env, M, k): it calls k() once per answer (bindings in place) and returns
  // OK, or STOP (a consumer wants no more answers), or CUT (a cut was reached: drop the remaining alternatives)
  Interp.prototype.compileGoal = function (g, slot) {
    g = D(g); const k = P.key(g);
    const self = this;
    switch (k) {
      case ',/2': {
        // runs of deterministic goals become one in-place test (no continuation closures)
        const flat = P.flatConj(g); const parts = [];
        for (let i = 0; i < flat.length;) {
          if (this.isDet(flat[i])) { let j = i; while (j < flat.length && this.isDet(flat[j])) j++; parts.push({ test: this.compileTest(flat.slice(i, j), slot) }); i = j; }
          else { parts.push({ goal: this.compileGoal(flat[i], slot) }); i++; }
        }
        let c = null;
        for (let i = parts.length - 1; i >= 0; i--) {
          const p = parts[i], next = c;
          if (p.test) {
            const t = p.test;
            c = next ? (env, M, kk) => { const m = M.trail.length; if (!t(env, M)) { M.undo(m); return OK; } const s = next(env, M, kk); M.undo(m); return s; }
                     : (env, M, kk) => { const m = M.trail.length; if (!t(env, M)) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; };
          } else {
            const gi = p.goal;
            c = next ? (env, M, kk) => gi(env, M, () => next(env, M, kk)) : gi;
          }
        }
        return c;
      }
      case 'true/0': return (env, M, kk) => { M.tick(); return kk(); };
      case 'fail/0': case 'false/0': return (env, M) => { M.tick(); return OK; };
      case '!/0': return (env, M, kk) => { M.tick(); const s = kk(); return s === STOP ? STOP : CUT; };
      case ';/2': {
        const l = D(g.a[0]);
        if (l.t === 'c' && l.f === '->' && l.a.length === 2) return this.ite(l.a[0], l.a[1], g.a[1], slot);
        const A = this.compileGoal(g.a[0], slot), B = this.compileGoal(g.a[1], slot);
        return (env, M, kk) => { M.tick(); const s = A(env, M, kk); if (s !== OK) return s; return B(env, M, kk); };
      }
      case '->/2': return this.ite(g.a[0], g.a[1], P.FAIL, slot);
      case '\\+/1': {
        if (P.flatConj(g.a[0]).every(x => this.isDet(x))) {
          const t = this.compileTest(P.flatConj(g.a[0]), slot);
          return (env, M, kk) => { M.tick(); const m = M.trail.length; const r = t(env, M); M.undo(m); return r ? OK : kk(); };
        }
        const G = this.compileGoal(g.a[0], slot);
        return (env, M, kk) => { M.tick(); let found = false; const m = M.trail.length; G(env, M, () => { found = true; return STOP; }); M.undo(m); return found ? OK : kk(); };
      }
      case 'findall/3': {
        const T = this.compileBuild(g.a[0], slot), G = this.compileGoal(g.a[1], slot), L = this.compileBuild(g.a[2], slot);
        return (env, M, kk) => {
          M.tick(); const res = []; const m = M.trail.length;
          G(env, M, () => { res.push(P.resolve(T(env))); return OK; });
          M.undo(m);
          const m2 = M.trail.length;
          if (!M.unify(L(env), list(res))) { M.undo(m2); return OK; }
          const s = kk(); M.undo(m2); return s;
        };
      }
      case 'aggregate_all/3': {
        const spec = D(g.a[0]); const sp = spec.t === 'a' ? spec.n : spec.f;
        const T = spec.t === 'c' ? this.compileBuild(spec.a[0], slot) : () => P.TRUE;
        const G = this.compileGoal(g.a[1], slot), R = this.compileBuild(g.a[2], slot);
        return (env, M, kk) => {
          M.tick(); const res = []; const m = M.trail.length;
          G(env, M, () => { res.push(P.resolve(T(env))); return OK; });
          M.undo(m);
          const v = aggregate(sp, res); if (v === null) return OK;
          const m2 = M.trail.length;
          if (!M.unify(R(env), v)) { M.undo(m2); return OK; }
          const s = kk(); M.undo(m2); return s;
        };
      }
    }
    const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
    const build = env => { const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return a; };
    if (this.ir.has(k)) {
      // splice the callee's packet into the conjunction
      const r = this.ref(k);
      return (env, M, kk) => {
        const args = build(env);
        const pk = r.fn(args, M);
        for (let i = 0; i < pk.length; i++) {
          const it = pk[i];
          if (it.out !== undefined) { M.write(it.out); continue; }
          M.tick();
          const m = M.trail.length; const row = it.row; let ok = true;
          for (let j = 0; j < n; j++) if (!M.unify(args[j], row[j])) { ok = false; break; }
          if (ok) { const s = kk(); M.undo(m); if (s !== OK) return s; } else M.undo(m);
        }
        return OK;
      };
    }
    if (k === '=/2') { const a = as[0], b = as[1]; return (env, M, kk) => { M.tick(); const m = M.trail.length; if (!M.unify(a(env), b(env))) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; }; }
    const bi = P.builtins[k];
    if (bi && bi.nondet) {
      return (env, M, kk) => {
        M.tick(); const a = build(env); const m = M.trail.length; const it = bi.fn(a, M, null);
        for (;;) {
          const r = it.next(); if (r.done) break;
          M.tick();
          const s = kk();
          if (s !== OK) { M.undo(m); return s; }
          if (r.value === 'last') break;
        }
        M.undo(m); return OK;
      };
    }
    if (bi && bi.call) {
      // higher-order builtins that the converter did not specialise (maplist on a variable closure, phrase, ...)
      return (env, M, kk) => { M.tick(); const ng = bi.fn(build(env), M, null); if (ng === null) return OK; return self.dynamicGoal(ng, M, kk); };
    }
    if (bi) return (env, M, kk) => { M.tick(); const a = build(env); const m = M.trail.length; if (!bi.fn(a, M, null)) { M.undo(m); return OK; } const s = kk(); M.undo(m); return s; };
    return () => { throw new Error('Detlog interpreter: unknown procedure ' + k); };
  };
  // deterministic goals: builtins that are neither nondeterministic nor higher-order (their packet has at most one row)
  Interp.prototype.isDet = function (g) {
    g = D(g); const k = P.key(g);
    if (k === 'true/0' || k === 'fail/0' || k === 'false/0' || k === '=/2') return true;
    if (!k || this.ir.has(k)) return false;
    const b = P.builtins[k]; return !!(b && !b.nondet && !b.call);
  };
  // a run of deterministic goals as one boolean test; bindings stay in place (the caller undoes them)
  Interp.prototype.compileTest = function (gs, slot) {
    const ts = gs.map(g => {
      g = D(g); const k = P.key(g);
      if (k === 'true/0') return (env, M) => { M.tick(); return true; };
      if (k === 'fail/0' || k === 'false/0') return (env, M) => { M.tick(); return false; };
      const as = g.t === 'c' ? g.a.map(x => this.compileBuild(x, slot)) : []; const n = as.length;
      if (k === '=/2') { const a = as[0], b = as[1]; return (env, M) => { M.tick(); return M.unify(a(env), b(env)); }; }
      const fn = P.builtins[k].fn;
      if (n === 2) { const a0 = as[0], a1 = as[1]; return (env, M) => { M.tick(); return fn([a0(env), a1(env)], M, null); }; }
      return (env, M) => { M.tick(); const a = new Array(n); for (let i = 0; i < n; i++) a[i] = as[i](env); return fn(a, M, null); };
    });
    if (ts.length === 1) return ts[0];
    const n = ts.length;
    return (env, M) => { for (let i = 0; i < n; i++) if (!ts[i](env, M)) return false; return true; };
  };
  Interp.prototype.ite = function (C, T, F, slot) {
    const Tg = this.compileGoal(T, slot), Fg = this.compileGoal(F, slot);
    if (P.flatConj(C).every(x => this.isDet(x))) {
      const t = this.compileTest(P.flatConj(C), slot);
      return (env, M, kk) => { M.tick(); const m = M.trail.length; if (t(env, M)) { const s = Tg(env, M, kk); M.undo(m); return s; } M.undo(m); return Fg(env, M, kk); };
    }
    const Cg = this.compileGoal(C, slot);
    return (env, M, kk) => {
      M.tick();
      let found = false, ts = OK; const m = M.trail.length;
      Cg(env, M, () => { found = true; ts = Tg(env, M, kk); return STOP; });
      M.undo(m);
      return found ? ts : Fg(env, M, kk);
    };
  };
  // a goal built at run time (rare): compiled on the fly with no clause variables
  Interp.prototype.dynamicGoal = function (g, M, kk) {
    const vars = termVars(g); const slot = new Map(); const env = vars.slice(); vars.forEach((v, i) => slot.set(v, i));
    return this.compileGoal(g, slot)(env, M, kk);
  };
  function aggregate(sp, ts) {
    switch (sp) {
      case 'count': return Int(ts.length);
      case 'sum': { let s = Int(0); for (const x of ts) s = P.evalArith(Cmp('+', [s, x])); return s; }
      case 'max': if (!ts.length) return null; return ts.map(P.evalArith).reduce((m, x) => x.v > m.v ? x : m);
      case 'min': if (!ts.length) return null; return ts.map(P.evalArith).reduce((m, x) => x.v < m.v ? x : m);
      case 'bag': return list(ts);
      case 'set': return list(P.sortUnique(ts));
    }
    throw new Error('aggregate_all: unknown spec ' + sp);
  }

  const cache = new WeakMap();
  function runDetlogInterp(conv, qpred, varNames, opts) {
    opts = opts || {};
    let I = cache.get(conv); if (!I) { I = new Interp(conv); cache.set(conv, I); }
    const M = new Machine(opts);
    const vs = varNames.map(n => Var(n)); const k = qpred + '/' + varNames.length;
    const t0 = P.now(); let items = null, error = null, limit = false;
    try { const r = I.preds.get(k); if (!r) throw new Error('no query predicate ' + k); M.items = []; items = r.fn(vs, M); }
    catch (e) {
      if (e instanceof RangeError) return Object.assign(runFallback(conv, qpred, varNames, opts), { engine: 'Detlog engine (interpreter ran out of JS stack)' });
      error = e.limit ? e.message : e.prolog ? (e.term ? P.errText(e.term) : e.message) : e.message; limit = !!e.limit;
    }
    const t1 = P.now();
    const events = [], answers = []; let output = '';
    if (items) for (const it of items) {
      if (it.out !== undefined) { output += it.out; const l = events[events.length - 1]; if (l && l.k === 'out') l.text += it.out; else events.push({ k: 'out', text: it.out }); continue; }
      const nm = P.namer(); const text = varNames.length ? varNames.map((n, i) => n + ' = ' + P.show(it.row[i], { varName: nm })).join(', ') : 'true';
      answers.push({ text }); events.push({ k: 'row', text });
    }
    return { ok: !error, answers, events, output, steps: M.steps, cps: 0, maxCP: 0, calls: M.calls, packetRows: M.rows, timeMs: t1 - t0, error, limit, engine: 'interpreter', violations: 0, violationPreds: [] };
  }
  function runFallback(conv, qpred, varNames, opts) { return P.runDetlogFast(P.loadProgram(conv.text), qpred, varNames, opts); }
  P.DetlogInterp = Interp; P.runDetlogInterp = runDetlogInterp;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
