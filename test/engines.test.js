// engines.test.js - the deterministic engine's tiers agree with each other on every example query, plain and MNN:
//   * the JIT and the closure compiler: same answers, steps, decisions and violations (native tier off);
//   * the native tier on and off: same answers and errors (it counts a native call as one step, so steps differ).
// Extra queries exercise the native tier's bail-outs (non-integers, unbound arguments, errors).
'use strict';
const test = require('node:test'), assert = require('node:assert');
const path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'cgen', 'proof', 'stats', 'cref', 'examples']) require(path.join(__dirname, '..', 'src', f + '.js'));
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

// The C export: every example built with the native tier (modes from a profile run) and without it prints the
// same answers.  Error queries are left out (the C runtime stops at an error); edge queries where native code
// must bail out to the generic code (a float in arithmetic) are in.
test('C export: native tier on and off print the same answers', (t) => {
  const cp = require('child_process'), fs = require('fs'), os = require('os');
  try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { t.skip('no C compiler'); return; }
  P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '..', 'src', 'runtime.c'), 'utf8');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-cnat-'));
  const CEXTRA = { lists: ['doubles([1,2.5], D)', 'app([1,2], Y, [1,2,3])', 'numlist(1, 120, L), nrev(L, R)', 'nrev([A,B], R)'], fib: ['fib(24, F)', 'fib(N, 5)'], queens: ['queens(5, Qs)'] };
  let natives = 0;
  for (const ex of P.EXAMPLES) {
    const qs = ex.queries.concat(CEXTRA[ex.id] || []).filter(q => !P.runQuery(P.loadProgram(ex.src), P.readTerm(q), { stepLimit: 3e6, maxAnswers: 1000 }).error);
    const conv = P.convert(ex.src, { mnn: true, queries: qs });
    const outs = [];
    for (const native of [false, true]) {
      const { code } = P.toC(conv.text, { queries: conv.queries, native });
      if (native) natives += (code.match(/^static int nat\d+\(/gm) || []).length;
      const f = path.join(dir, ex.id + (native ? '_n' : '_g'));
      fs.writeFileSync(f + '.c', code);
      cp.execSync('cc -O2 -w -o ' + f + ' ' + f + '.c -lm');
      outs.push(cp.execFileSync(f).toString().split('\n').filter(l => !l.startsWith('% steps') && !l.startsWith('% hand-written')).join('\n'));
    }
    assert.strictEqual(outs[1], outs[0], ex.id);
  }
  assert.ok(natives >= 10, natives + ' native C functions');
});

// The C export's own reading: for a query that runs a benchmark algorithm, the program includes the hand-written
// C (only when its answers are exactly the program's) and prints its speed as a % of C's.
test('C export: % of C\'s speed for benchmark queries', (t) => {
  const cp = require('child_process'), fs = require('fs'), os = require('os');
  try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { t.skip('no C compiler'); return; }
  P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '..', 'src', 'runtime.c'), 'utf8');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-cref-'));
  const cases = [['fib', 'fib(16, F)', 'fib'], ['lists', 'numlist(1, 40, L), nrev(L, R)', 'nrev'], ['lists', 'numlist(1, 100, L), doubles(L, D), total(D, S)', 'doubles'],
    ['queens', 'queens(5, Qs)', 'queens'], ['splice', 'pin(A, B, C)', 'pin'], ['unfold', 'anc(X, dee)', 'anc']];
  for (const [id, q, alg] of cases) {
    const ex = P.EXAMPLES.find(e => e.id === id);
    const conv = P.convert(ex.src, { mnn: true, queries: [q] });
    const r = P.toC(conv.text, { queries: conv.queries });
    assert.deepStrictEqual(r.refs, [q], id);
    const f = path.join(dir, alg); fs.writeFileSync(f + '.c', r.code); cp.execSync('cc -O2 -w -o ' + f + ' ' + f + '.c -lm');
    const out = cp.execFileSync(f, ['-r', '20']).toString();
    const m = out.match(/^% hand-written C \((\w+)\): ([0-9.]+) ms per run; this program runs at ([0-9.e+]+)% of C's speed$/m);
    assert.ok(m, out); assert.strictEqual(m[1], alg); assert.ok(+m[3] > 0, out);
  }
  // no reference when the program's answers are not the algorithm's
  const other = P.convert('fib(N, F) :- F is N * 2.', { mnn: true, queries: ['fib(10, F)'] });
  assert.deepStrictEqual(P.toC(other.text, { queries: other.queries }).refs, []);
});
