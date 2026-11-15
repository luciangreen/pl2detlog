// engines.test.js - the deterministic engine's tiers agree with each other on every example query, plain and MNN:
//   * the JIT and the closure compiler: same answers, steps, decisions and violations (native tier off);
//   * the native tier on and off: same answers and errors (it counts a native call as one step, so steps differ).
// Extra queries exercise the native tier's bail-outs (non-integers, unbound arguments, errors).
'use strict';
const test = require('node:test'), assert = require('node:assert');
const path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'cgen', 'proof', 'stats', 'examples']) require(path.join(__dirname, '..', 'src', f + '.js'));
const P = globalThis.PL2D;
const EXTRA = {
  lists: ['app([1,2], [3], R)', 'app([1,2], Y, [1,2,3])', 'total([1,a], S)', 'doubles([1,2.5], D)', 'nrev([A,B], R)', 'numlist(1, 120, L), nrev(L, R)'],
  cuts: ['classify(a, C)', 'max(1, 1.0, Z)'],
  queens: ['queens(0, Qs)', 'safe([1,a])', 'queens(5, Qs)'],
  fib: ['fib(a, F)', 'fib(N, 5)', 'fib(-3, F)', 'fib(24, F)'],
};
const norm = x => String(x).replace(/_G\d+/g, '_G');
const run = (prog, q) => P.runDetlogFast(prog, q.pred, q.vars, { stepLimit: 6e7 });
const restore = () => { P.DETLOG_JIT = true; P.DETLOG_NATIVE = true; };

test('JIT and closure compiler agree exactly (native tier off)', () => {
  try {
    for (const ex of P.EXAMPLES) for (const mnn of [false, true]) {
      const conv = P.convert(ex.src, { mnn, queries: ex.queries.concat(EXTRA[ex.id] || []) });
      const pc = P.loadProgram(conv.text), pj = P.loadProgram(conv.text);
      P.DETLOG_NATIVE = false;
      for (const q of conv.queries) {
        P.DETLOG_JIT = false; const a = run(pc, q);
        P.DETLOG_JIT = true; const b = run(pj, q);
        assert.ok(b.engine.includes('JIT'), ex.id + ': ' + q.text + ' ran on ' + b.engine);
        assert.strictEqual(norm(JSON.stringify(b.events)), norm(JSON.stringify(a.events)), ex.id + ' ' + (mnn ? 'MNN' : 'plain') + ': ' + q.text);
        assert.deepStrictEqual([b.steps, b.decisions, b.violations, norm(b.error)], [a.steps, a.decisions, a.violations, norm(a.error)], ex.id + ' ' + (mnn ? 'MNN' : 'plain') + ': ' + q.text);
      }
    }
  } finally { restore(); }
});

test('native tier on and off give the same answers and errors', () => {
  let used = 0;
  try {
    for (const ex of P.EXAMPLES) {
      const conv = P.convert(ex.src, { mnn: true, queries: ex.queries.concat(EXTRA[ex.id] || []) });
      const p1 = P.loadProgram(conv.text), p2 = P.loadProgram(conv.text);
      for (const q of conv.queries) {
        P.DETLOG_NATIVE = false; const a = run(p1, q);
        P.DETLOG_NATIVE = true; const b = run(p2, q);
        if (b.steps < a.steps) used++;
        assert.strictEqual(norm(JSON.stringify(b.events)), norm(JSON.stringify(a.events)), ex.id + ': ' + q.text);
        assert.strictEqual(norm(b.error), norm(a.error), ex.id + ': ' + q.text);
      }
    }
  } finally { restore(); }
  assert.ok(used >= 10, 'the native tier ran on ' + used + ' queries');
});
