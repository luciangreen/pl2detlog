// reference.js - the example algorithms written directly in JavaScript, the same way as reference.c:
// the floor for any engine running in JavaScript.  Lists are cons objects.  Prints  name<TAB>us<TAB>check.
'use strict';
const cons = (h, t) => ({ h, t });
const time = (name, fn, check) => {
  let n = 0; const w = performance.now(); let r;
  while (performance.now() - w < 150) { r = fn(); n++; }
  const ts = []; for (let b = 0; b < 3; b++) { const t = performance.now(); for (let i = 0; i < n; i++) r = fn(); ts.push((performance.now() - t) / n * 1000); }
  ts.sort((a, b) => a - b); console.log(name + '\t' + ts[1].toFixed(4) + '\t' + check(r));
};
function fib(n) { if (n === 0) return 0; if (n === 1) return 1; return fib(n - 1) + fib(n - 2); }
function app(a, l) { return a === null ? l : cons(a.h, app(a.t, l)); }
function nrev(l) { return l === null ? null : app(nrev(l.t), cons(l.h, null)); }
function numlist(lo, hi) { let r = null; for (let i = hi; i >= lo; i--) r = cons(i, r); return r; }
function doubles(l) { return l === null ? null : cons(2 * l.h, doubles(l.t)); }
function total(l) { let s = 0; for (; l !== null; l = l.t) s += l.h; return s; }
function safe(qs) { for (let i = 0; i < qs.length; i++) for (let j = i + 1, d = 1; j < qs.length; j++, d++) if (qs[i] === qs[j] + d || qs[i] === qs[j] - d) return false; return true; }
// permutations in permutation/2's order (each remaining element first in turn), tested as they are made
function queens(n) {
  const sols = [], out = new Array(n), used = new Array(n).fill(false);
  (function perm(k) {
    if (k === n) { if (safe(out)) sols.push(out.slice()); return; }
    for (let i = 0; i < n; i++) if (!used[i]) { used[i] = true; out[k] = i + 1; perm(k + 1); used[i] = false; }
  })(0);
  return sols;
}
function pin() { const r = []; for (let a = 0; a <= 9; a++) for (let b = 0; b <= 9; b++) for (let c = 0; c <= 9; c++) if (a + b + c === 25) r.push([a, b, c]); return r; }
const par = [[0, 1], [1, 2], [2, 3]];
function ancBB(z, y) { let n = 0; for (const [a, b] of par) if (a === z && b === y) n++; for (const [a, b] of par) if (a === z) n += ancBB(b, y); return n; }
function anc(y) { const r = []; for (const [a, b] of par) if (b === y) r.push(a); for (const [a, b] of par) for (let k = ancBB(b, y); k > 0; k--) r.push(a); return r; }

time('fib(18, F)', () => fib(18), r => r);
time('fib(21, F)', () => fib(21), r => r);
time('numlist(1, 60, L), nrev(L, R)', () => nrev(numlist(1, 60)), r => r.h);
time('numlist(1, 300, L), nrev(L, R)', () => nrev(numlist(1, 300)), r => r.h);
time('numlist(1, 2000, L), doubles(L, D), total(D, S)', () => total(doubles(numlist(1, 2000))), r => r);
time('queens(6, Qs)', () => queens(6), r => r.length);
time('queens(7, Qs)', () => queens(7), r => r.length);
time('pin(A, B, C)', () => pin(), r => r.length);
time('anc(X, dee)', () => anc(3), r => r.length);
