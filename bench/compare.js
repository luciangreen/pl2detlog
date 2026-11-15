// compare.js - the example algorithms in hand-written C (bench/reference.c) and JavaScript (bench/reference.js)
// against Prolog, the Detlog interpreter, converted Detlog, MNN Detlog (JIT) and MNN Detlog's C export.
// Prolog and the Detlog engines are timed per run including the text of their answers; "MNN compute" is MNN
// Detlog's own run time without formatting answers, which is what the references measure.
//   node bench/compare.js [--json out.json] [--no-export]
// Times are microseconds per run: the JS engines are warmed up and timed for about 300 ms each (median of
// 3 batches); reference.c and the C export (./p -r N) time themselves in-process.
'use strict';
const fs = require('fs'), cp = require('child_process'), path = require('path'), os = require('os');
const root = path.resolve(__dirname, '..');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'cgen', 'proof', 'stats', 'examples']) require(path.join(root, 'src', f + '.js'));
const P = globalThis.PL2D;
P.C_RUNTIME = fs.readFileSync(path.join(root, 'src', 'runtime.c'), 'utf8');
const args = process.argv.slice(2);
const jsonOut = args.includes('--json') ? args[args.indexOf('--json') + 1] : null;
const exportC = !args.includes('--no-export');

const CASES = [
  ['fib', 'fib(18, F)'], ['fib', 'fib(21, F)'],
  ['lists', 'numlist(1, 60, L), nrev(L, R)'], ['lists', 'numlist(1, 300, L), nrev(L, R)'],
  ['lists', 'numlist(1, 2000, L), doubles(L, D), total(D, S)'],
  ['queens', 'queens(6, Qs)'], ['queens', 'queens(7, Qs)'],
  ['splice', 'pin(A, B, C)'], ['unfold', 'anc(X, dee)'],
];

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-bench-'));
cp.execSync('cc -O2 -w -o ' + tmp + '/reference ' + path.join(__dirname, 'reference.c'));
const ref = new Map(cp.execSync(tmp + '/reference').toString().trim().split('\n').map(l => { const [q, us] = l.split('\t'); return [q, +us]; }));
const refJs = new Map(cp.execSync(process.execPath + ' ' + path.join(__dirname, 'reference.js')).toString().trim().split('\n').map(l => { const [q, us] = l.split('\t'); return [q, +us]; }));

const time = fn => { let n = 0; const w = performance.now(); while (performance.now() - w < 100) { fn(); n++; } const ts = []; for (let b = 0; b < 3; b++) { const t = performance.now(); for (let i = 0; i < n; i++) fn(); ts.push((performance.now() - t) / n * 1000); } ts.sort((a, b) => a - b); return ts[1]; };
const median = xs => xs.slice().sort((a, b) => a - b)[xs.length >> 1];
// the C export times itself in-process: ./p -r N repeats each query N times and prints ms per run
function cExport(conv) {
  const { code } = P.toC(conv.text, { queries: conv.queries });
  fs.writeFileSync(tmp + '/p.c', code); cp.execSync('cc -O2 -w -o ' + tmp + '/p ' + tmp + '/p.c -lm');
  const per = reps => { const out = cp.execFileSync(tmp + '/p', ['-r', String(reps)], { stdio: 'pipe' }).toString(); const m = out.match(/([0-9.]+) ms per run/); return m ? +m[1] * 1000 : NaN; };
  const est = per(1);
  const reps = Math.max(1, Math.min(1e6, Math.round(300000 / Math.max(est, 0.05))));
  return median([per(reps), per(reps), per(reps)]);
}

const rows = [];
for (const [id, q] of CASES) {
  const ex = P.EXAMPLES.find(e => e.id === id);
  const plain = P.convert(ex.src, { mnn: false, queries: [q] }), mnn = P.convert(ex.src, { mnn: true, queries: [q] });
  const pp = P.loadProgram(plain.text), pm = P.loadProgram(mnn.text), sp = P.loadProgram(ex.src), pq = P.readTerm(q);
  const a = plain.queries[0], b = mnn.queries[0];
  const chk = P.runDetlogFast(pm, b.pred, b.vars, { stepLimit: 1e10 }), chp = P.runQuery(sp, pq, { stepLimit: 1e9, maxAnswers: 100000 });
  const same = JSON.stringify(chk.answers) === JSON.stringify(chp.answers.map(x => x));
  const r = {
    query: q, c: ref.get(q),
    prolog: time(() => P.runQuery(sp, pq, { stepLimit: 1e9, maxAnswers: 100000 })),
    interp: time(() => P.runDetlogInterp(plain, a.pred, a.vars, { stepLimit: 1e10 })),
    detlog: time(() => P.runDetlogFast(pp, a.pred, a.vars, { stepLimit: 1e10 })),
    mnn: time(() => P.runDetlogFast(pm, b.pred, b.vars, { stepLimit: 1e10 })),
    mnnCompute: (() => { const ts = []; let tot = 0, n = 0; const w = performance.now(); while (performance.now() - w < 300) { tot += P.runDetlogFast(pm, b.pred, b.vars, { stepLimit: 1e10 }).timeMs; n++; } return tot / n * 1000; })(),
    js: refJs.get(q),
    mnnC: exportC ? cExport(mnn) : null, engine: chk.engine, answers: chk.answers.length, same,
  };
  rows.push(r);
  const f = x => x === null || x === undefined ? '—' : x < 10 ? x.toFixed(2) : x < 1000 ? x.toFixed(1) : Math.round(x).toString();
  console.log([q.padEnd(48), 'C ' + f(r.c), 'JS ' + f(r.js), 'prolog ' + f(r.prolog), 'interp ' + f(r.interp), 'detlog ' + f(r.detlog), 'MNN ' + f(r.mnn), 'MNN compute ' + f(r.mnnCompute), 'MNN-C ' + f(r.mnnC), 'compute/C ' + (r.mnnCompute / r.c).toFixed(1) + 'x', 'compute/JS ' + (r.mnnCompute / r.js).toFixed(1) + 'x', r.same ? '' : 'ANSWERS DIFFER'].join('  '));
}
if (jsonOut) fs.writeFileSync(jsonOut, JSON.stringify(rows, null, 1));
