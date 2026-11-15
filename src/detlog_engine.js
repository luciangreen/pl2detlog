/* pl2detlog Detlog engine: runs converted Detlog without choicepoints.
   Every call commits to the single clause its first argument selects; if_commit/3 is the only decision
   construct (the head of its condition, else branch only when the condition has no answer).
   Calls where more than one clause matches are counted as determinism violations. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show, variantKey } = P;
  const D = deref;

  function DetEngine(prog, opts) {
    opts = opts || {};
    this.prog = prog; this.trail = []; this.steps = 0; this.decisions = 0; this.violations = []; this.maxDecisionDepth = 0;
    this.out = ''; this.stepLimit = opts.stepLimit || 2e7; this.memo = new Map(); this.memoHits = 0; this.memoStores = 0;
    this.globals = new Map(); this.rowsBuilt = 0; this.maxRows = 0;
    this.depth = 0;
    // index clauses by first-argument functor
    this.index = new Map();
    for (const [k, cls] of prog.preds) this.index.set(k, cls);
  }
  DetEngine.prototype.bind = function (v, t) { v.ref = t; this.trail.push(v); };
  DetEngine.prototype.undo = function (mark) { const tr = this.trail; while (tr.length > mark) tr.pop().ref = null; };
  DetEngine.prototype.unify = P.Engine.prototype.unify;
  DetEngine.prototype.write = function (s) { this.out += s; };
  DetEngine.prototype.tick = function (n) { this.steps += n || 1; if (this.steps > this.stepLimit) throw new P.LimitError('step limit (' + this.stepLimit + ') exceeded'); };

  DetEngine.prototype.solve = function (goal) {
    const self = this;
    let goals = { g: goal, next: null };
    const marks = [];
    const fail = () => {
      if (!marks.length) return false;
      const m = marks.pop(); self.undo(m.trail); goals = m.els; return true;
    };
    for (;;) {
      if (goals === null) return true;
      const fr = goals; goals = fr.next;
      const g = D(fr.g);
      self.tick();
      let f, a;
      if (g.t === 'a') { f = g.n; a = []; } else if (g.t === 'c') { f = g.f; a = g.a; } else throw P.typeError('callable', g);
      const k = f + '/' + a.length;
      switch (k) {
        case 'true/0': continue;
        case 'fail/0': case 'false/0': if (!fail()) return false; continue;
        case ',/2': self.steps--; goals = { g: a[0], next: { g: a[1], next: goals } }; continue;
        case 'if_commit/3': {
          self.decisions++;
          const mk = { trail: self.trail.length, els: { g: a[2], next: goals } };
          marks.push(mk); if (marks.length > self.maxDecisionDepth) self.maxDecisionDepth = marks.length;
          goals = { g: a[0], next: { g: Cmp('$commit', [{ t: 'n', v: 0, mk }]), next: { g: a[1], next: goals } } };
          continue;
        }
        case '$commit/1': { const mk = a[0].mk; const i = marks.lastIndexOf(mk); if (i >= 0) marks.splice(i, 1); self.steps--; continue; }
        case ';/2': case '->/2': case '\\+/1': case '!/0': case 'findall/3': case 'call/1':
          throw new Error('Detlog engine: ' + k + ' is not Detlog (the converted program must not contain it)');
      }
      const cls = self.index.get(k);
      if (cls) {
        // first-argument selection
        let chosen = -1; const m0 = self.trail.length; let body = null;
        // first-argument indexing, as SWI-Prolog does it: more than one compatible clause = a choicepoint
        const cand = [];
        for (let i = 0; i < cls.length; i++) if (!a.length || P.firstArgMayMatch(a[0], cls[i].head.a[0])) cand.push(i);
        if (cand.length > 1 && self.violations.length < 1000) self.violations.push(k);
        for (const i of cand) {
          const cl = cls[i];
          const mp = new Map(); const h = copy(cl.head, mp);
          if (self.unify(h, g)) { chosen = i; body = copy(cl.body, mp); break; }
          self.undo(m0);
        }
        if (chosen < 0) { if (!fail()) return false; continue; }
        const bd = D(body);
        if (!(bd.t === 'a' && bd.n === 'true')) goals = { g: body, next: goals };
        continue;
      }
      const rb = RUNTIME[k] || (P.builtins[k] && !P.builtins[k].nondet && !P.builtins[k].call ? P.builtins[k].fn : null);
      if (rb) {
        const mark = self.trail.length;
        if (!rb(a, self, g)) { self.undo(mark); if (!fail()) return false; }
        continue;
      }
      if (P.builtins[k]) throw new Error('Detlog engine: nondeterministic builtin ' + k + ' called directly (it must be wrapped in builtin_rows/2)');
      throw new Error('Detlog engine: unknown procedure ' + k);
    }
  };
  // would clause head `head` match goal g as the call was (before bindings made after mark m0)?
  DetEngine.prototype.unifyProbe = function (head, g, m0) {
    // snapshot the bindings made since m0, undo them, test, then redo
    const made = this.trail.slice(m0).map(v => [v, v.ref]);
    for (let i = made.length - 1; i >= 0; i--) made[i][0].ref = null;
    const save = this.trail.length; this.trail.length = m0;
    const mk = this.trail.length;
    const ok = this.unify(copy(head), g);
    this.undo(mk);
    for (const [v, r] of made) v.ref = r;
    this.trail.length = m0; for (const [v] of made) this.trail.push(v);
    return ok;
  };

  // ---------------- runtime (deterministic, no choicepoints) ----------------
  const RUNTIME = {};
  const R = (k, fn) => { RUNTIME[k] = fn; };
  const items = t => { const a = listToArray(t); if (!a) throw new Error('packet is not a proper list: ' + show(t)); return a; };
  const isOut = t => { t = D(t); return t.t === 'c' && t.f === 'out' && t.a.length === 1; };
  const isRow = t => { t = D(t); return t.t === 'c' && t.f === 'e' && t.a.length === 1; };
  const isCut = t => { t = D(t); return t.t === 'a' && t.n === 'cut'; };
  // cut markers: a cut reached on a row emits [cut, e(Row)]; loops stop after it, concatenations drop what follows
  const hasCut = xs => xs.some(isCut);
  R('rows_concat_cut/2', (a, e) => { const ls = items(a[0]); let all = []; for (const l of ls) { const x = items(l); e.tick(x.length); all = all.concat(x); if (hasCut(x)) break; } return e.unify(a[1], list(all)); });
  R('rows_cut_concat/2', (a, e) => { const ls = items(a[0]); let all = []; for (const l of ls) { const x = items(l); e.tick(x.length); all = all.concat(x.filter(y => !isCut(y))); if (hasCut(x)) break; } return e.unify(a[1], list(all)); });
  R('strip_cut/2', (a, e) => { const x = items(a[0]); e.tick(x.length); return e.unify(a[1], list(x.filter(y => !isCut(y)))); });
  R('cut_in/2', (a, e) => { if (!isRow(a[0])) return false; const x = items(a[1]); e.tick(); return hasCut(x); });
  R('rows_concat/2', (a, e) => { const ls = items(a[0]); let all = []; for (const l of ls) { const x = items(l); e.tick(x.length); all = all.concat(x); } e.rowsBuilt += all.length; if (all.length > e.maxRows) e.maxRows = all.length; return e.unify(a[1], list(all)); });
  // splice_extend(Packet, Pattern, e(Env), Out)
  R('splice_extend/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it);
      if (isOut(x) || isCut(x)) { res.push(x); continue; }
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x.a[0])) res.push(P.resolve(c.a[1]));
      e.undo(mk);
    }
    e.rowsBuilt += res.length; if (res.length > e.maxRows) e.maxRows = res.length;
    return e.unify(a[3], list(res));
  });
  // project_rows(EnvPacket, EnvVars, HeadArgs, Rows)
  R('project_rows/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it);
      if (isOut(x) || isCut(x)) { res.push(x); continue; }
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x.a[0])) res.push(Cmp('e', [P.resolve(c.a[1])]));
      e.undo(mk);
    }
    return e.unify(a[3], list(res));
  });
  // project_list(Rows, e(EnvPattern), Template, Values)
  R('project_list/4', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const x = D(it); if (!isRow(x)) continue;
      const c = copy(Cmp('-', [a[1], a[2]]));
      const mk = e.trail.length;
      if (e.unify(c.a[0], x)) res.push(P.resolve(c.a[1]));
      e.undo(mk);
    }
    return e.unify(a[3], list(res));
  });
  R('packet_first/3', (a, e) => {
    const xs = items(a[0]); const pre = [];
    for (const x of xs) { e.tick(); if (isCut(x)) continue; if (isOut(x)) { pre.push(D(x)); continue; } return e.unify(a[1], list(pre)) && e.unify(a[2], list([x])); }
    return e.unify(a[1], list(pre)) && e.unify(a[2], NIL);
  });
  R('packet_split/3', (a, e) => { const outs = [], rows = []; for (const x of items(a[0])) { e.tick(); if (isCut(x)) continue; (isOut(x) ? outs : rows).push(D(x)); } return e.unify(a[1], list(outs)) && e.unify(a[2], list(rows)); });
  R('effect_text/2', (a, e) => {
    const g = D(a[0]); const k = P.key(g); const bi = P.builtins[k];
    if (!bi) throw new Error('effect_text: unknown output builtin ' + k);
    const saveOut = e.out; e.out = '';
    try { bi.fn(g.t === 'c' ? g.a : [], e, g); } finally { var txt = e.out; e.out = saveOut; }
    return e.unify(a[1], Str(txt));
  });
  R('builtin_rows/2', (a, e) => {
    const g = D(a[0]); const k = P.key(g); const bi = P.builtins[k];
    if (!bi || !bi.nondet) throw new Error('builtin_rows: ' + k + ' is not a nondeterministic builtin');
    const res = []; const mk = e.trail.length;
    const it = bi.fn(g.t === 'c' ? g.a : [], e, g);
    let guard = 0;
    for (;;) {
      const r = it.next(); if (r.done) break;
      e.tick(); res.push(Cmp('e', [list([copy(g)])]));
      if (++guard > 1e6 || res.length > 1e6) throw new P.LimitError('builtin_rows: infinite generator ' + k + ' (no finite packet)');
      if (e.steps > e.stepLimit) throw new P.LimitError('step limit exceeded');
    }
    e.undo(mk);
    return e.unify(a[1], list(res));
  });
  R('cp_filter/3', (a, e) => {
    const res = [];
    for (const it of items(a[0])) {
      e.tick();
      const c = copy(a[1]); const f = copy(D(it).a[0]);
      const mk = e.trail.length;
      if (e.unify(c, f)) res.push(Cmp('e', [P.resolve(c)]));
      e.undo(mk);
    }
    return e.unify(a[2], list(res));
  });
  R('aggregate_list/3', (a, e) => {
    const sp = D(a[0]).n; const ts = items(a[1]); e.tick(ts.length);
    let r;
    switch (sp) {
      case 'count': r = Int(ts.length); break;
      case 'sum': { let s = Int(0); for (const x of ts) s = P.evalArith(Cmp('+', [s, x])); r = s; break; }
      case 'max': if (!ts.length) return false; r = ts.map(P.evalArith).reduce((m, x) => x.v > m.v ? x : m); break;
      case 'min': if (!ts.length) return false; r = ts.map(P.evalArith).reduce((m, x) => x.v < m.v ? x : m); break;
      case 'bag': r = list(ts); break;
      case 'set': r = list(P.sortUnique(ts)); break;
      default: throw new Error('aggregate_list: unknown spec ' + sp);
    }
    return e.unify(a[2], r);
  });
  R('splice_safe/2', (a) => { const va = new Set(termVars(a[0])); return !termVars(a[1]).some(v => va.has(v)); });
  R('splice2/6', (a, e) => {
    const PA = items(a[0]), PB = items(a[1]); const res = [];
    for (const ra of PA) {
      if (isOut(ra)) { res.push(D(ra)); continue; }
      for (const rb of PB) {
        e.tick();
        if (isOut(rb)) continue;
        const c = copy(Cmp('f', [a[2], a[3], a[4]]));
        const mk = e.trail.length;
        if (e.unify(c.a[0], D(ra).a[0]) && e.unify(c.a[1], D(rb).a[0])) res.push(P.resolve(c.a[2]));
        e.undo(mk);
      }
    }
    e.rowsBuilt += res.length;
    return e.unify(a[5], list(res));
  });
  R('memo_lookup/3', (a, e) => {
    const key = variantKey(Cmp('k', [a[0], a[1]]));
    const hit = e.memo.get(key);
    if (hit) { e.memoHits++; e.tick(); return e.unify(a[2], Cmp('found', [renameRows(hit, a[1])])); }
    return e.unify(a[2], Atom('none'));
  });
  // rows were stored relative to a variant of the call; rebuild them for this call's variables
  function renameRows(stored, callArgs) {
    const c = copy(stored); // c = f(StoredArgs, Rows)
    const mk = [];
    // map stored call variables onto this call's variables (variant => bijection)
    const sv = termVars(c.a[0]), cv = termVars(callArgs);
    sv.forEach((v, i) => { v.ref = cv[i]; mk.push(v); });
    const r = P.resolve(c.a[1]);
    for (const v of mk) v.ref = null;
    return r;
  }
  R('memo_store/3', (a, e) => {
    const key = variantKey(Cmp('k', [a[0], a[1]]));
    if (!e.memo.has(key)) { e.memo.set(key, copy(Cmp('f', [a[1], a[2]]))); e.memoStores++; }
    return true;
  });
  // s2a_rows(s2a(K, Cols), Args, Rows)
  R('s2a_rows/3', (a, e) => {
    const spec = D(a[0]); const K = D(spec.a[0]).v; const cols = items(spec.a[1]).map(D); const args = items(a[1]);
    const val = (c, I) => {
      if (c.f === 'const') return c.a[0];
      if (c.f === 'data') return items(c.a[0])[I];
      const ds = items(c.a[0]).map(x => D(x).v); let s = 0; for (let d = 0; d < ds.length; d++) s += ds[d] * binom(I, d); return Int(s);
    };
    // direct solve on a bound linear column
    let only = null;
    for (let j = 0; j < cols.length; j++) {
      const c = cols[j], x = D(args[j]);
      if (c.f === 'newton' && x.t === 'n' && !x.f) {
        const ds = items(c.a[0]).map(y => D(y).v);
        if (ds.length === 2 && ds[1] !== 0) { const q = (x.v - ds[0]) / ds[1]; only = Number.isInteger(q) && q >= 0 && q < K ? [q] : []; break; }
      }
    }
    const idx = only || Array.from({ length: K }, (_, i) => i);
    const res = [];
    for (const I of idx) {
      e.tick();
      const row = cols.map(c => val(c, I));
      const c = copy(list(args)); const mk = e.trail.length;
      if (e.unify(c, list(row))) res.push(Cmp('e', [P.resolve(c)]));
      e.undo(mk);
    }
    return e.unify(a[2], list(res));
  });
  function binom(n, k) { let r = 1; for (let i = 0; i < k; i++) r = r * (n - i) / (i + 1); return Math.round(r); }
  R('detlog_unsupported/2', (a) => { throw new Error('not converted: ' + show(a[0]) + ': ' + P.textOf(a[1])); });
  P.binom = binom;
  P.DETLOG_RUNTIME = RUNTIME;

  // run a converted query predicate '$queryN'/k: returns events like runQuery
  function runDetlog(prog, qpred, varNames, opts) {
    opts = opts || {};
    const eng = new DetEngine(prog, opts);
    const vs = varNames.map(n => Var(n)); const Rv = Var('R');
    const goal = Cmp(qpred + '__cp', vs.concat([Rv]));
    const t0 = P.now(); let ok = false, error = null;
    try { ok = eng.solve(goal); } catch (e) { error = e.message; if (opts.debug) console.error(e); }
    const t1 = P.now();
    const events = [], answers = []; let output = '';
    if (ok) {
      for (const it of listToArray(Rv) || []) {
        const x = D(it);
        if (x.t === 'a') continue;
        if (x.f === 'out') { const txt = P.textOf(x.a[0]); output += txt; const last = events[events.length - 1]; if (last && last.k === 'out') last.text += txt; else events.push({ k: 'out', text: txt }); continue; }
        const row = listToArray(x.a[0]); const nm = P.namer();
        const text = varNames.length ? varNames.map((n, i) => n + ' = ' + show(row[i], { varName: nm })).join(', ') : 'true';
        answers.push({ text }); events.push({ k: 'row', text });
      }
    } else if (!error) error = 'Detlog query failed (a packet predicate must always succeed)';
    return { ok: !error, answers, events, output, steps: eng.steps, decisions: eng.decisions, violations: eng.violations.length, violationPreds: [...new Set(eng.violations)], cps: 0, maxCP: 0, timeMs: t1 - t0, error, memoHits: eng.memoHits, memoStores: eng.memoStores, rowsBuilt: eng.rowsBuilt, maxRows: eng.maxRows };
  }
  P.DetEngine = DetEngine; P.runDetlog = runDetlog;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
