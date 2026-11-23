// The exported Detlog in real SWI-Prolog (skipped without swipl): for every example, plain and MNN, in the
// stream form (with src/detlog_stream_rt.pl) and the packet form, each query prints what the source
// program prints in this app's Prolog.
const { test } = require('node:test');
const assert = require('node:assert/strict');
const cp = require('child_process'), fs = require('fs'), os = require('os'), path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'stream', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'algebra', 'rewrite', 'cgen', 'proof', 'stats', 'cref', 'examples']) require('../src/' + f + '.js');
const P = globalThis.PL2D;
const RT = fs.readFileSync(path.join(__dirname, '../src/detlog_runtime.pl'), 'utf8');
const SRT = fs.readFileSync(path.join(__dirname, '../src/detlog_stream_rt.pl'), 'utf8');
const render = evs => evs.map(e => e.k === 'out' ? e.text : e.text + '\n').join('');
test('SWI-Prolog runs the exported Detlog (streams and packets) as the source runs', (t) => {
  try { cp.execSync('swipl --version', { stdio: 'ignore' }); } catch (e) { t.skip('no swipl'); return; }
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-swi-'));
  for (const ex of P.EXAMPLES) for (const mnn of [false, true]) {
    const qs = ex.queries.filter(q => { const r = P.runQuery(P.loadProgram(ex.src), P.readTerm(q), { stepLimit: 3e6, maxAnswers: 1000 }); return !r.error && !r.truncated; });
    const conv = P.convert(ex.src, { mnn, queries: qs });
    for (const [form, text, rt] of [['streams', conv.text, RT + '\n' + SRT], ['packets', conv.packetText, RT]]) {
      const f = path.join(dir, ex.id + (mnn ? '_m_' : '_p_') + form + '.pl');
      const main = conv.queries.map(q => "  write('?- " + q.text.replace(/\\/g, '\\\\').replace(/'/g, "\\'") + ".'), nl, \\+ \\+ ('" + q.pred + "__cp'(" + q.vars.concat(['R__']).join(', ') + '), detlog_print([' + q.vars.map(v => "'" + v + "'").join(', ') + '], R__))').join(',\n');
      fs.writeFileSync(f, ':- style_check(-singleton).\n:- style_check(-discontiguous).\n' + rt + '\n' + text + '\nmain :-\n' + (main || '  true') + '.\n');
      const got = cp.execFileSync('swipl', ['-q', '-g', 'main', '-t', 'halt', f], { stdio: ['ignore', 'pipe', 'pipe'], timeout: 60000 }).toString();
      const exp = conv.queries.map(q => '?- ' + q.text + '.\n' + render(P.runQuery(P.loadProgram(ex.src), q.text, { stepLimit: 3e6 }).events)).join('');
      // SWI-Prolog writes [1,2] where this app writes [1, 2]: compared without the space after a comma
      const norm = x => x.replace(/, /g, ',');
      assert.equal(norm(got), norm(exp), ex.id + (mnn ? ' MNN ' : ' plain ') + form);
    }
  }
});
