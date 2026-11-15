// npm test: every example must convert, prove, back-convert, compile to C and run on the Prolog runtime.
for (const f of ['core','engine','builtins','convert','detlog_engine','detlog_fast','detlog_interp','backconv','cgen','proof','stats','examples']) require('../src/'+f+'.js');
const P = globalThis.PL2D; const fs = require('fs'); const cp = require('child_process'); const os = require('os'); const path = require('path');
P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '../src/runtime.c'), 'utf8');
const RT = fs.readFileSync(path.join(__dirname, '../src/detlog_runtime.pl'), 'utf8');
let haveCC = true; try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { haveCC = false; }
const render = evs => { let s = '', rows = 0; for (const e of evs) { if (e.k === 'out') s += e.text; else { rows++; s += e.text + '\n'; } } return rows ? s : s + 'false\n'; };
let failures = 0; const fail = (id, m) => { failures++; console.log('  FAIL ' + id + ': ' + m); };
for (const ex of P.EXAMPLES) {
  const t0 = Date.now();
  const r = P.analyse(ex.src, ex.queries, { timing: false });
  const bad = r.proof.checks.filter(c => c.ok === false);
  bad.forEach(c => fail(ex.id, c.group + ': ' + c.name + ' — ' + c.detail));
  for (const conv of [r.plain, r.mnn]) {
    const label = ex.id + '/' + conv.mode;
    // Prolog runtime: exported Detlog run on a plain Prolog engine
    const prog = P.loadProgram(RT + '\n' + conv.text);
    for (const q of conv.queries) {
      const ref = r.runs.find(x => x.query === q.text);
      if (ref.prolog.error || ref.prolog.truncated) continue;
      const out = P.runQuery(prog, "'" + q.pred + "__cp'(" + q.vars.concat(['R__']).join(', ') + '), detlog_print([' + q.vars.map(v => "'" + v + "'").join(',') + '], R__)', { stepLimit: 2e7 });
      if (out.output !== render(ref.prolog.events).replace(/false\n$/, '')) fail(label, 'Prolog-runtime run of ' + q.text + ' differs');
    }
    if (haveCC) {
      const { code } = P.toC(conv.text, { queries: conv.queries });
      const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-')); const cf = path.join(dir, 'p.c'), bin = path.join(dir, 'p');
      fs.writeFileSync(cf, code);
      try { cp.execSync('cc -O1 -w -o ' + bin + ' ' + cf + ' -lm', { stdio: 'pipe' }); } catch (e) { fail(label, 'C compile: ' + e.stderr.toString().split('\n')[0]); continue; }
      let got = ''; try { got = cp.execSync(bin, { timeout: 60000 }).toString(); } catch (e) { got = (e.stdout || '').toString(); }
      got = got.split('\n').filter(l => !l.startsWith('% steps')).join('\n');
      let exp = ''; for (const q of conv.queries) { const ref = r.runs.find(x => x.query === q.text); if (ref.prolog.error) { exp = null; break; } exp += '?- ' + q.text + '.\n' + render(ref.prolog.events); }
      if (exp !== null && got.trim() !== exp.trim()) fail(label, 'C output differs');
    }
  }
  console.log((bad.length ? 'FAIL ' : 'ok   ') + ex.id.padEnd(10) + ' ' + r.proof.checks.length + ' proof checks, ' + r.runs.length + ' queries, ' + (Date.now() - t0) + ' ms');
}
console.log(failures ? failures + ' failure(s)' : 'all examples pass' + (haveCC ? '' : ' (no C compiler: C not checked)'));
process.exit(failures ? 1 : 0);
