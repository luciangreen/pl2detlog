/* pl2detlog C reference: how a query's time compares with the same algorithm written by hand in C.
   The app can't compile C, so it times the hand-written JavaScript version of the algorithm (as in
   bench/reference.js) on this machine and scales it by C's time over JavaScript's for that algorithm, as
   measured by bench/compare.js (cc -O2 and Node).  A reference applies to a query only when its answers are
   exactly the program's answers, so a program that defines fib/2 differently gets no C comparison. */
(function (P) {
  'use strict';
  const cons = (h, t) => ({ h, t });
  const toArr = l => { const a = []; for (; l !== null; l = l.t) a.push(l.h); return a; };
  const show = a => '[' + a.join(', ') + ']';
  function fib(n) { if (n === 0) return 0; if (n === 1) return 1; return fib(n - 1) + fib(n - 2); }
  function app(a, l) { return a === null ? l : cons(a.h, app(a.t, l)); }
  function nrev(l) { return l === null ? null : app(nrev(l.t), cons(l.h, null)); }
  function numlist(lo, hi) { let r = null; for (let i = hi; i >= lo; i--) r = cons(i, r); return r; }
  function doubles(l) { return l === null ? null : cons(2 * l.h, doubles(l.t)); }
  function total(l) { let s = 0; for (; l !== null; l = l.t) s += l.h; return s; }
  function safe(qs) { for (let i = 0; i < qs.length; i++) for (let j = i + 1, d = 1; j < qs.length; j++, d++) if (qs[i] === qs[j] + d || qs[i] === qs[j] - d) return false; return true; }
  function queens(n) {
    const sols = [], out = new Array(n), used = new Array(n).fill(false);
    (function perm(k) {
      if (k === n) { if (safe(out)) sols.push(out.slice()); return; }
      for (let i = 0; i < n; i++) if (!used[i]) { used[i] = true; out[k] = i + 1; perm(k + 1); used[i] = false; }
    })(0);
    return sols;
  }
  function pin() { const r = []; for (let a = 0; a <= 9; a++) for (let b = 0; b <= 9; b++) for (let c = 0; c <= 9; c++) if (a + b + c === 25) r.push([a, b, c]); return r; }
  const par = [[0, 1], [1, 2], [2, 3]], PEOPLE = ['ann', 'bob', 'cy', 'dee'];
  function ancBB(z, y) { let n = 0; for (const [a, b] of par) if (a === z && b === y) n++; for (const [a, b] of par) if (a === z) n += ancBB(b, y); return n; }
  function anc(y) { const r = []; for (const [a, b] of par) if (b === y) r.push(a); for (const [a, b] of par) for (let k = ancBB(b, y); k > 0; k--) r.push(a); return r; }

  // C time / JavaScript time per algorithm (bench/results.json: hand-written C with cc -O2, hand-written JS on Node)
  const C_OVER_JS = { fib: 0.143, nrev: 0.50, doubles: 0.41, queens: 0.21, pin: 0.39, anc: 0.0105 };
  const N = s => { const n = +s; return Number.isInteger(n) && n >= 0 ? n : null; };
  // each: query pattern -> { alg, run: () => result, rows: result -> expected answer texts }; sizes are capped
  // so that the reference never takes long (the query itself has already run)
  const REFS = [
    [/^fib\((\d+),\s*F\)$/, m => { const n = N(m[1]); return n !== null && n <= 32 && { alg: 'fib', n, run: () => fib(n), rows: v => ['F = ' + v] }; }],
    [/^numlist\(1,\s*(\d+),\s*L\),\s*nrev\(L,\s*R\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 3000 && { alg: 'nrev', n, run: () => nrev(numlist(1, n)), rows: r => { const a = toArr(r); return ['L = ' + show(a.slice().reverse()) + ', R = ' + show(a)]; } }; }],
    [/^numlist\(1,\s*(\d+),\s*L\),\s*doubles\(L,\s*D\),\s*total\(D,\s*S\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 100000 && { alg: 'doubles', n, run: () => total(doubles(numlist(1, n))), rows: s => { const a = toArr(numlist(1, n)); return ['L = ' + show(a) + ', D = ' + show(a.map(x => 2 * x)) + ', S = ' + s]; } }; }],
    [/^queens\((\d+),\s*Qs\)$/, m => { const n = N(m[1]); return n !== null && n >= 1 && n <= 9 && { alg: 'queens', n, run: () => queens(n), rows: s => s.map(q => 'Qs = ' + show(q)) }; }],
    [/^pin\(A,\s*B,\s*C\)$/, () => ({ alg: 'pin', n: 0, run: pin, rows: s => s.map(([a, b, c]) => 'A = ' + a + ', B = ' + b + ', C = ' + c) })],
    [/^anc\(X,\s*dee\)$/, () => ({ alg: 'anc', n: 3, run: () => anc(3), rows: s => s.map(i => 'X = ' + PEOPLE[i]) })],
  ];
  // ms per run, timed in batches (the clock is read per batch, not per run, as nanosecond runs need):
  // after a warm-up, the batch size is set so a batch takes about 4 ms; the median of 3 batches
  let sink = 0;
  function batchTime(fn) {
    const w = P.now(); while (P.now() - w < 60) sink ^= (fn() ? 1 : 0); // warm-up, so the code is optimised
    let n = 1;
    for (;;) { const t = P.now(); for (let i = 0; i < n; i++) sink ^= (fn() ? 1 : 0); const dt = P.now() - t; if (dt > 4 || n >= 1 << 24) break; n = dt < 0.5 ? n * 8 : Math.ceil(n * 4.5 / dt); }
    const ts = [];
    for (let b = 0; b < 3; b++) { const t = P.now(); for (let i = 0; i < n; i++) sink ^= (fn() ? 1 : 0); ts.push((P.now() - t) / n); }
    return ts.sort((a, b) => a - b)[1];
  }
  // q: the query text; events: the program's answer events.  Returns null, or
  // { alg, jsMs (hand-written JavaScript, timed here), cMs (estimated C on this machine), ratio }
  // the benchmark algorithm a query runs, or null: its pattern matches (cRefPattern) and the hand-written
  // version's answers are exactly the program's answers (cRefMatch)
  function cRefPattern(q) {
    q = q.trim().replace(/\.\s*$/, '');
    for (const [re, mk] of REFS) { const m = q.match(re); if (m) return mk(m) || null; }
    return null;
  }
  function cRefMatch(q, events) {
    const ref = cRefPattern(q); if (!ref) return null;
    const exp = ref.rows(ref.run());
    if (!events || events.some(e => e.k !== 'row') || events.length !== exp.length || events.some((e, i) => e.text !== exp[i])) return null;
    return ref;
  }
  function cReference(q, events) {
    const ref = cRefMatch(q, events); if (!ref) return null;
    const jsMs = batchTime(ref.run);
    return { alg: ref.alg, jsMs, cMs: jsMs * C_OVER_JS[ref.alg], ratio: C_OVER_JS[ref.alg] };
  }
  // the C export of the MNN Detlog against the hand-written C, both compiled with cc -O2 on one machine
  // (bench/results.json; µs per run)
  const C_EXPORT_RECORDED = {
    "fib(18, F)": { c: 2.9501, mnnC: 2.6 },
    "fib(21, F)": { c: 15.713, mnnC: 4 },
    "numlist(1, 60, L), nrev(L, R)": { c: 5.1872, mnnC: 17.1 },
    "numlist(1, 300, L), nrev(L, R)": { c: 161.4897, mnnC: 475.7 },
    "numlist(1, 2000, L), doubles(L, D), total(D, S)": { c: 10.9991, mnnC: 106 },
    "queens(6, Qs)": { c: 8.2256, mnnC: 132.8 },
    "queens(7, Qs)": { c: 62.2202, mnnC: 1005.5 },
    "pin(A, B, C)": { c: 0.5094, mnnC: 4.1 },
    "anc(X, dee)": { c: 0.0025, mnnC: 3.6 }
  };
  P.cReference = cReference; P.cRefPattern = cRefPattern; P.cRefMatch = cRefMatch; P.C_OVER_JS = C_OVER_JS; P.C_EXPORT_RECORDED = C_EXPORT_RECORDED;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
