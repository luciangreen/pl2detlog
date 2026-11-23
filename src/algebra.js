/* pl2detlog algebra: rewrites that change the algorithm, each derived from first principles, with its
   proof obligation stated where it is used.  Shared by the source rewrites (rewrite.js), the JIT and the C
   export.

   pairwise(prog, key): is the test predicate key (one argument, a list) a conjunction over all pairs of
   positions?  That is, is it
       t([]).
       t([X|Xs]) :- r(X, Xs, C0), t(Xs).          (the two goals in either order)
       r(_, [], _).
       r(X, [Y|Ys], D) :- Tests(X, Y, D), D1 is D + 1, r(X, Ys, D1).
   with Tests a conjunction of integer comparisons over X, Y and D alone?  Then, unfolding both
   recursions on a proper list L = [L1, ..., Ln]:
       t(L)  <=>  for all i < j:  Tests(Li, Lj, C0 + (j - i - 1)).
   A conjunction over pairs is prefix-closed: if any pair inside a prefix fails, every completion of the
   prefix fails.  So a generator that builds L left to right may test each new element against those
   already placed, and drop the prefix at the first failure: the same lists pass, in the same order. */
(function (P) {
  'use strict';
  const D = P.deref;
  const CMP = { '=\\=': '!=', '=:=': '==', '<': '<', '>': '>', '=<': '<=', '>=': '>=' };
  const isV = t => D(t).t === 'v';
  const conjOf = b => P.flatConj ? P.flatConj(b).map(D) : (function f(g) { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? f(g.a[0]).concat(f(g.a[1])) : [g]; })(b);
  const isNil = t => { t = D(t); return t.t === 'a' && t.n === '[]'; };
  const consOf = t => { t = D(t); return t.t === 'c' && t.f === '.' && t.a.length === 2 ? [D(t.a[0]), D(t.a[1])] : null; };
  const isTrue = b => { b = D(b); return b.t === 'a' && b.n === 'true'; };
  const keyOf = g => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };

  // an integer expression over the given variables, as a function from variable names to code
  function arithOK(t, vars) {
    t = D(t);
    if (t.t === 'n') return !t.f && Number.isSafeInteger(t.v);
    if (t.t === 'v') return vars.includes(t);
    return t.t === 'c' && ((t.a.length === 2 && ['+', '-', '*'].includes(t.f)) || (t.a.length === 1 && t.f === '-')) && t.a.every(a => arithOK(a, vars));
  }
  function arithCode(t, env) {
    t = D(t);
    if (t.t === 'n') return '(' + t.v + ')';
    if (t.t === 'v') return env.get(t);
    if (t.a.length === 1) return '(-' + arithCode(t.a[0], env) + ')';
    return '(' + arithCode(t.a[0], env) + ' ' + t.f + ' ' + arithCode(t.a[1], env) + ')';
  }

  function pairwise(prog, key) {
    const tc = prog.preds.get(key);
    if (!tc || tc.length !== 2 || +key.slice(key.lastIndexOf('/') + 1) !== 1) return null;
    const name = key.slice(0, key.lastIndexOf('/'));
    const base = tc.find(c => isNil(D(c.head).a[0]) && isTrue(c.body));
    const step = tc.find(c => c !== base);
    if (!base || !step) return null;
    const sc = consOf(D(step.head).a[0]); if (!sc || !isV(sc[0]) || !isV(sc[1]) || sc[0] === sc[1]) return null;
    const [X, Xs] = sc;
    const sb = conjOf(step.body); if (sb.length !== 2) return null;
    const self = sb.find(g => keyOf(g) === key), rel = sb.find(g => g !== self);
    if (!self || !rel || D(self.a[0]) !== Xs) return null;
    const rk = keyOf(rel); if (!rk || !rk.endsWith('/3') || rk === key) return null;
    if (D(rel.a[0]) !== X || D(rel.a[1]) !== Xs) return null;
    const c0 = D(rel.a[2]); if (c0.t !== 'n' || c0.f || !Number.isSafeInteger(c0.v)) return null;
    const rc = prog.preds.get(rk);
    if (!rc || rc.length !== 2) return null;
    const rbase = rc.find(c => isNil(D(c.head).a[1]) && isTrue(c.body) && isV(D(c.head).a[0]) && isV(D(c.head).a[2]));
    const rstep = rc.find(c => c !== rbase);
    if (!rbase || !rstep) return null;
    const h = D(rstep.head); const Q = D(h.a[0]), Dv = D(h.a[2]); const yc = consOf(h.a[1]);
    if (!isV(Q) || !isV(Dv) || !yc || !isV(yc[0]) || !isV(yc[1])) return null;
    const [Y, Ys] = yc;
    if (new Set([Q, Dv, Y, Ys]).size !== 4) return null;
    const rb = conjOf(rstep.body);
    const rec = rb[rb.length - 1];
    if (keyOf(rec) !== rk || D(rec.a[0]) !== Q || D(rec.a[1]) !== Ys) return null;
    const D1 = D(rec.a[2]); if (!isV(D1)) return null;
    const inc = rb[rb.length - 2];
    if (!inc || keyOf(inc) !== 'is/2' || D(inc.a[0]) !== D1) return null;
    const ie = D(inc.a[1]);
    const plus1 = ie.t === 'c' && ie.f === '+' && ie.a.length === 2 && ((D(ie.a[0]) === Dv && D(ie.a[1]).t === 'n' && D(ie.a[1]).v === 1) || (D(ie.a[1]) === Dv && D(ie.a[0]).t === 'n' && D(ie.a[0]).v === 1));
    if (!plus1) return null;
    const tests = rb.slice(0, -2);
    for (const g of tests) {
      if (g.t !== 'c' || g.a.length !== 2 || !CMP[g.f]) return null;
      if (!g.a.every(a => arithOK(a, [Q, Y, Dv]))) return null;
    }
    return {
      name, key, rel: rk, c0: c0.v, tests, vars: { Q, Y, D: Dv },
      // C (or JavaScript) for Tests(prev, next, dist): integer expressions in, a condition out
      code: (prev, next, dist, js) => tests.length ? tests.map(g => '(' + arithCode(g.a[0], new Map([[Q, prev], [Y, next], [Dv, dist]])) + ' ' + (js ? ({ '!=': '!==', '==': '===' })[CMP[g.f]] || CMP[g.f] : CMP[g.f]) + ' ' + arithCode(g.a[1], new Map([[Q, prev], [Y, next], [Dv, dist]])) + ')').join(' && ') : '1',
      proof: 'pairwise test: ' + name + '(L) holds iff for all i < j, ' + tests.map(g => P.show(g)).join(', ') + ' with ' + P.show(Q) + ' = L_i, ' + P.show(Y) + ' = L_j, ' + P.show(Dv) + ' = ' + c0.v + ' + (j - i - 1) (unfolding ' + key + ' and ' + rk + '); a conjunction over pairs is prefix-closed, so each new element is tested against those placed and a failing prefix is dropped'
    };
  }

  P.pairwise = pairwise;
  P.algebra = { arithOK, arithCode, conjOf, keyOf, consOf, isNil };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
