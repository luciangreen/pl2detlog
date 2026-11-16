// algebra.test.js - the first-principles rewrites (src/rewrite.js, src/algebra.js) keep every answer:
//   * each source rewrite fires where it should, and the rewritten program gives the original's answers,
//     in order, on the Prolog engine (including the cases a rewrite must leave alone);
//   * the C export with the rewrites, unchecked, prints what the C export without them prints, checked.
'use strict';
const test = require('node:test'), assert = require('node:assert');
const path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'algebra', 'rewrite', 'cgen', 'proof', 'stats', 'cref', 'examples']) require(path.join(__dirname, '..', 'src', f + '.js'));
const P = globalThis.PL2D;

const answers = (src, q) => { const r = P.runQuery(P.loadProgram(src), P.readTerm(q), { stepLimit: 3e6, maxAnswers: 2000 }); return r.error ? 'error: ' + P.show(r.error) : r.answers.map(a => a.text).join('\n'); };

const CASES = [
  { name: 'accumulate (nrev)', rule: 'accumulate',
    src: 'nrev([], []).\nnrev([H|T], R) :- nrev(T, RT), app(RT, [H], R).\napp([], L, L).\napp([H|T], L, [H|R]) :- app(T, L, R).\n',
    queries: ['nrev([1,2,3,4], R)', 'nrev([], R)', 'nrev([a,B,c], R)', 'nrev(L, [1,2])', 'nrev([1,2], [2,1])', 'nrev([1,2], [1,2])', 'numlist(1, 50, L), nrev(L, R)'] },
  { name: 'accumulate (append/3, two elements)', rule: 'accumulate',
    src: 'dup([], []).\ndup([H|T], R) :- dup(T, RT), append(RT, [H, H], R).\n',
    queries: ['dup([1,2,3], R)', 'dup([], R)', 'dup([x], [x,x])'] },
  { name: 'solve for the last generator', rule: 'solve',
    src: 'd(X) :- between(0, 9, X).\npin(A, B, C) :- d(A), d(B), d(C), A + B + C =:= 25.\nq(X, Y) :- between(1, 5, X), between(1, 20, Y), Y - X =:= 3.\nr(X, Y) :- between(1, 5, X), between(1, 20, Y), 10 =:= X - Y + 12.\n',
    queries: ['pin(A, B, C)', 'pin(9, B, C)', 'pin(A, B, 1)', 'q(X, Y)', 'r(X, Y)'] },
  { name: 'fuse the map into the fold', rule: 'mapfold',
    src: 'double(X, Y) :- Y is 2 * X.\nadd(X, A0, A) :- A is A0 + X.\ndoubles(L, D) :- maplist(double, L, D).\ntotal(L, S) :- foldl(add, L, 0, S).\nboth(L, D, S) :- doubles(L, D), total(D, S).\n',
    queries: ['both([1,2,3], D, S)', 'both([], D, S)', 'both([1,a], D, S)', 'both([1,2], D, 6)', 'both([1,2], D, 7)', 'both(L, D, S)'], limit: true },
  { name: 'left alone: a non-unit coefficient', rule: null,
    src: 'p(X, Y) :- between(1, 9, X), between(1, 9, Y), 2 * Y =:= X.\n', queries: ['p(X, Y)'] },
  { name: 'left alone: a fold that can fail', rule: null,
    src: 'double(X, Y) :- Y is 2 * X.\npos(X, A0, A) :- X > 0, A is A0 + X.\nb(L, D, S) :- maplist(double, L, D), foldl(pos, D, 0, S).\n', queries: ['b([1,2], D, S)', 'b([1,-2], D, S)'] },
];

for (const c of CASES) {
  test('rewrite: ' + c.name, () => {
    const rw = P.rewrite(c.src);
    if (c.rule) assert.ok(rw.steps.some(s => s.rule === c.rule), 'rule ' + c.rule + ' fired: ' + JSON.stringify(rw.steps.map(s => s.rule)));
    else assert.strictEqual(rw.steps.length, 0, 'no rewrite');
    for (const s of rw.steps) assert.ok(s.proof && s.proof.length > 20, 'a derivation is given');
    for (const q of c.queries) {
      if (c.limit && /^both\(L/.test(q)) { // an unbound list: both enumerate lists by length; compare the first answers
        const first = (src) => P.runQuery(P.loadProgram(src), P.readTerm(q), { stepLimit: 2e5, maxAnswers: 4 }).answers.map(a => a.text.replace(/_G?\d+/g, '_')).join('\n');
        assert.strictEqual(first(rw.text), first(c.src), q); continue;
      }
      assert.strictEqual(answers(rw.text, q).replace(/_G?\d+/g, '_'), answers(c.src, q).replace(/_G?\d+/g, '_'), c.name + ': ' + q);
    }
  });
}

test('rewrite: a query is fused like a body (convert)', () => {
  const ex = P.EXAMPLES.find(e => e.id === 'lists');
  const conv = P.convert(ex.src, { mnn: true, queries: ['numlist(1, 5, L), doubles(L, D), total(D, S)'] });
  assert.ok(conv.algebra.some(s => s.rule === 'mapfold'));
  const off = P.convert(ex.src, { mnn: true, algebra: false, queries: ['numlist(1, 5, L), doubles(L, D), total(D, S)'] });
  assert.strictEqual(off.algebra.length, 0);
});

test('algebra: the pairwise test of queens is found', () => {
  const ex = P.EXAMPLES.find(e => e.id === 'queens');
  const prog = P.loadProgram(ex.src);
  const keys = prog.order.filter(k => P.pairwise(prog, k));
  assert.ok(keys.length >= 1, 'a pairwise predicate: ' + keys);
  const pw = P.pairwise(prog, keys[0]);
  assert.ok(pw.proof && /prefix/.test(pw.proof));
});

// with the rewrites and unchecked, the C export prints what it prints without them, checked
test('C export: the rewrites and the unchecked runtime print the same answers', (t) => {
  const cp = require('child_process'), fs = require('fs'), os = require('os');
  try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { t.skip('no C compiler'); return; }
  P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '..', 'src', 'runtime.c'), 'utf8');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-alg-'));
  const RUNS = [['lists', ['numlist(1, 300, L), nrev(L, R)', 'numlist(1, 2000, L), doubles(L, D), total(D, S)', 'nrev([a,b], R)']],
    ['queens', ['queens(6, Qs)', 'queens(7, Qs)', 'queens(4, Qs)']], ['splice', ['pin(A, B, C)']], ['unfold', ['anc(X, dee)']], ['fib', ['fib(21, F)']]];
  for (const [id, qs] of RUNS) {
    const ex = P.EXAMPLES.find(e => e.id === id);
    const outs = [];
    for (const [algebra, checked] of [[false, true], [true, false]]) {
      const conv = P.convert(ex.src, { mnn: true, algebra, queries: qs });
      const f = path.join(dir, id + (algebra ? '_a' : '_p'));
      fs.writeFileSync(f + '.c', P.toC(conv.text, { queries: conv.queries, source: conv.source, checked }).code);
      cp.execSync('cc -O2 -w -o ' + f + ' ' + f + '.c -lm');
      outs.push(cp.execFileSync(f, ['--no-ref']).toString().split('\n').filter(l => !l.startsWith('%')).join('\n'));
    }
    assert.strictEqual(outs[1], outs[0], id);
  }
});

// the JIT prunes the same way when it knows the source (prog.pairwiseSource), with the same answers
test('JIT: pairwise-pruned permutations give the same answers', () => {
  const ex = P.EXAMPLES.find(e => e.id === 'queens');
  for (const q of ['queens(6, Qs)', 'queens(8, Qs)', 'queens(3, Qs)']) {
    const c = P.convert(ex.src, { mnn: true, queries: [q] }); const qq = c.queries[0];
    const run = (pw) => { const pr = P.loadProgram(c.text); if (pw) pr.pairwiseSource = P.loadProgram(c.source); return P.runDetlogFast(pr, qq.pred, qq.vars, { stepLimit: 1e9 }).answers.map(a => a.text); };
    assert.deepStrictEqual(run(true), run(false), q);
  }
});
