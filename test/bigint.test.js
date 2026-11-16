// Unbounded integers, as in SWI-Prolog: exact on the reference engine, and the JIT and native tier
// (the C route's analysis) bail out to the generic code before a result leaves the safe integers.
const { test } = require('node:test');
const assert = require('node:assert/strict');
require('../dist/pl2detlog.js');
const P = globalThis.PL2D;

const ans = (src, q) => { const r = P.runQuery(src, q); return r.error ?? r.answers.map((a) => a.text).join('; '); };
const FACT = 'fact(N, F) :- ( N =:= 0 -> F = 1 ; M is N - 1, fact(M, G), F is N * G ).';

test('arithmetic beyond 2^53 is exact', () => {
  assert.equal(ans('', 'X is 2**100'), 'X = 1267650600228229401496703205376');
  assert.equal(ans('', 'X is 9007199254740991 + 2'), 'X = 9007199254740993');
  assert.equal(ans('', 'X is 2**100 - 2**100 + 1, integer(X)'), 'X = 1');
  assert.equal(ans('', 'X is 123456789012345678901234567890 mod 7'), 'X = 0');
  assert.equal(ans('', 'X is -(2**70) // 3, Y is -(2**70) div 3, Z is -(2**70) mod 3'), 'X = -393530540239137101141, Y = -393530540239137101142, Z = 2');
  assert.equal(ans('', 'X is 2**70 / 2**68'), 'X = 4');
  assert.equal(ans('', 'X is 1 << 80, Y is msb(X)'), 'X = 1208925819614629174706176, Y = 80');
  assert.equal(ans('', 'X = 99999999999999999999, Y is X + 1'), 'X = 99999999999999999999, Y = 100000000000000000000');
  assert.equal(ans('', 'X is 2**64, X =:= 18446744073709551616.0'), 'X = 18446744073709551616');
  assert.equal(ans('', 'succ(X, 9007199254740993)'), 'X = 9007199254740992');
  assert.equal(ans('', 'msort([3, 2**60, 1.5], L)'), 'L = [1.5, 3, 2**60]');
  assert.equal(ans('', 'X is round(-2.5)'), 'X = -3');
});

test('the converted routes give the same big answers as Prolog', () => {
  for (const n of [20, 21, 25, 30]) {
    const q = `fact(${n}, F)`;
    const want = ans(FACT, q);
    assert.match(want, /^F = \d+$/);
    const c = P.convert(FACT, { mnn: true, queries: [q] });
    const prog = P.loadProgram(c.text);
    for (const native of [true, false]) {
      P.DETLOG_NATIVE = native;
      const r = P.runDetlogFast(prog, c.queries[0].pred, c.queries[0].vars, {});
      assert.equal(r.answers.map((a) => a.text).join('; '), want, `${q}, native ${native}`);
    }
  }
  P.DETLOG_NATIVE = true;
});
