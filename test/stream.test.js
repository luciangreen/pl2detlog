// Stream code (src/stream.js): Detlog without answer packets.  For every example, plain and MNN, the
// stream program gives Prolog's answers and output on the JIT and on the closure engine, no call has
// more than one candidate clause, and the code outside the stream library builds no packet and copies
// no environment.
const { test } = require('node:test');
const assert = require('node:assert/strict');
for (const f of ['core', 'engine', 'builtins', 'convert', 'stream', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'algebra', 'rewrite', 'cgen', 'proof', 'stats', 'cref', 'examples']) require('../src/' + f + '.js');
const P = globalThis.PL2D;
const render = evs => evs.map(e => e.k === 'out' ? e.text : e.text + '\n').join('');
const EXTRA = { lists: ['app(X, Y, [1,2,3])', 'numlist(1, 30, L), nrev(L, R)'], queens: ['queens(5, Qs)'], cuts: ['classify(7, C)', 'max(3, 9, M)'], scan: ['label([2,9,4], R)'] };
const PACKET = /\b(splice_extend|rows_concat|rows_cut_concat|project_rows|project_list|packet_first|packet_split|effect_text|cp_filter|splice2)\(/;

for (const ex of P.EXAMPLES) for (const mnn of [false, true]) {
  test(`streams: ${ex.id} (${mnn ? 'MNN' : 'plain'})`, () => {
    const qs = ex.queries.concat(EXTRA[ex.id] || []);
    const conv = P.convert(ex.src, { mnn, queries: qs });
    assert.ok(conv.streamText, conv.streamError || 'no stream code');
    // the query boundary ('$queryN__cp') is the packet interface every consumer reads: an S2A query
    // takes its rows from the table there (splice_extend), so the check is on the clauses before it
    const own = conv.streamText.split('% ---- stream library')[1].split('\n').slice(14).join('\n').split(/^'\$query\d+__cp'/m)[0];
    assert.ok(!PACKET.test(own), 'a packet builtin in the stream code');
    assert.ok(!/\bcopy_term\(/.test(own), 'an environment copy in the stream code');
    const prog = P.loadProgram(conv.streamText);
    for (const q of conv.queries) {
      const ref = P.runQuery(P.loadProgram(ex.src), q.text, { stepLimit: 2e7 });
      const fast = P.runDetlogFast(prog, q.pred, q.vars, { stepLimit: 6e7 });
      assert.equal(render(fast.events || []), render(ref.events || []), `${q.text} (JIT)`);
      const eng = new P.DetEngine(prog, { stepLimit: 6e7 });
      const R = P.Var('R');
      const ok = eng.solve(P.Cmp(q.pred + '__cp', q.vars.map(() => P.Var()).concat([R])));
      assert.ok(ok !== false, `${q.text} (closure engine) failed`);
      assert.deepEqual(eng.violations, [], `${q.text}: a call with more than one candidate clause`);
    }
  });
}

// The C export of stream code (bags, cut cells and direct output in src/runtime.c; the pruned permutation
// as a native loop) prints what the C export of packet code prints, plain and MNN, generic and native.
test('streams: C export prints the packet program\'s answers', (t) => {
  const cp = require('child_process'), fs = require('fs'), os = require('os'), path = require('path');
  try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { t.skip('no C compiler'); return; }
  P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '..', 'src', 'runtime.c'), 'utf8');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-cstream-'));
  for (const ex of P.EXAMPLES) for (const mnn of [false, true]) for (const native of [false, true]) {
    const qs = ex.queries.filter(q => !P.runQuery(P.loadProgram(ex.src), P.readTerm(q), { stepLimit: 3e6, maxAnswers: 1000 }).error);
    const conv = P.convert(ex.src, { mnn, queries: qs });
    const outs = [conv.text, conv.streamText].map((txt, i) => {
      const f = path.join(dir, ex.id + (mnn ? 'm' : 'p') + (native ? 'n' : 'g') + i);
      fs.writeFileSync(f + '.c', P.toC(txt, { queries: conv.queries, source: conv.source, native, checked: native }).code);
      cp.execSync('cc -O2 -w -o ' + f + ' ' + f + '.c -lm');
      return cp.execFileSync(f, ['--no-ref']).toString().split('\n').filter(l => !l.startsWith('% ')).join('\n');
    });
    assert.equal(outs[1], outs[0], ex.id + (mnn ? ' MNN' : ' plain') + (native ? ' native' : ''));
  }
});

// Deterministic integer code: same-name predicates of different arities (sumto/2, sumto/3) keep their own
// deterministic modes, and if-then-else on integers (collatz/2) runs in the native tier.
const INTS = `collatz(1, 0) :- !.
collatz(N, S) :- ( N mod 2 =:= 0 -> M is N // 2 ; M is 3 * N + 1 ), collatz(M, S0), S is S0 + 1.
gcd(A, 0, A) :- !.
gcd(A, B, G) :- C is A mod B, gcd(B, C, G).
ack(0, N, R) :- !, R is N + 1.
ack(M, 0, R) :- !, M1 is M - 1, ack(M1, 1, R).
ack(M, N, R) :- M1 is M - 1, N1 is N - 1, ack(M, N1, R1), ack(M1, R1, R).
digsum(0, 0) :- !.
digsum(N, S) :- D is N mod 10, N1 is N // 10, digsum(N1, S1), S is S1 + D.
maxc(N, M) :- findall(S, (between(1, N, I), collatz(I, S)), Ss), max_list(Ss, M).
sumto(N, S) :- sumto(N, 0, S).
sumto(0, A, A).
sumto(N, A, S) :- N > 0, A1 is A + N, N1 is N - 1, sumto(N1, A1, S).
`;
test('streams: deterministic integer code', () => {
  const qs = ['collatz(27, S)', 'gcd(1071, 462, G)', 'ack(2, 3, R)', 'digsum(987654321, S)', 'maxc(60, M)', 'sumto(500, S)', 'collatz(N, 3)'];
  for (const mnn of [false, true]) {
    const conv = P.convert(INTS, { mnn, queries: qs });
    const prog = P.loadProgram(conv.text);
    for (const q of conv.queries) {
      const ref = P.runQuery(P.loadProgram(INTS), q.text, { stepLimit: 2e7 });
      const r = P.runDetlogFast(prog, q.pred, q.vars, { stepLimit: 6e7 });
      assert.equal(render(r.events || []), render(ref.events || []), q.text + (mnn ? ' (MNN)' : ''));
      assert.equal(r.violations, 0, q.text + ': a call with more than one candidate clause');
    }
    if (mnn) {
      assert.equal((conv.text.match(/^sumto__d\(X__1, X__2, S__0\) :-/gm) || []).length, 1, 'sumto__d/3 once');
      assert.ok(P.nativeModesOf(prog).some(m => m.startsWith('collatz__d/3|')), 'collatz/2 runs natively');
    }
  }
});
