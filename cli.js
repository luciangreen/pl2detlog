#!/usr/bin/env node
// pl2detlog command line:  node cli.js prog.pl -q "fib(10, F)" [-q ...] [--plain] [--detlog out.pl] [--c out.c [--run [REPS]]] [--back out.pl] [--proof proof.txt] [--stats]
const fs = require('fs'); const path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'cgen', 'proof', 'stats', 'cref']) require('./src/' + f + '.js');
const P = globalThis.PL2D;
P.C_RUNTIME = fs.readFileSync(path.join(__dirname, 'src/runtime.c'), 'utf8');
const args = process.argv.slice(2); const qs = []; const o = {};
for (let i = 0; i < args.length; i++) {
  const a = args[i];
  if (a === '-q' || a === '--query') qs.push(args[++i]);
  else if (a.startsWith('--')) o[a.slice(2)] = (args[i + 1] && !args[i + 1].startsWith('-')) ? args[++i] : true;
  else o.file = a;
}
if (!o.file) { console.log('usage: node cli.js prog.pl -q QUERY [-q QUERY...] [--plain] [--detlog OUT.pl] [--c OUT.c [--run [REPS]]] [--back OUT.pl] [--proof OUT.txt] [--stats] [--sweep TEMPLATE --values 1..10]'); process.exit(1); }
const src = fs.readFileSync(o.file, 'utf8');
const r = P.analyse(src, qs, { timing: !!o.stats, sweep: o.sweep ? { template: o.sweep, values: o.values || '1..10' } : null });
if (r.errors.length) console.error(r.errors.join('\n'));
const conv = o.plain ? r.plain : r.mnn;
const rt = fs.readFileSync(path.join(__dirname, 'src/detlog_runtime.pl'), 'utf8');
if (o.detlog) fs.writeFileSync(o.detlog, ':- style_check(-singleton).\n' + rt + '\n' + conv.text);
else if (!o.c && !o.back && !o.proof && !o.stats) process.stdout.write(conv.text);
if (o.c) fs.writeFileSync(o.c, P.toC(conv.text, { queries: conv.queries }).code);
// --run: build the C with cc -O2 and run it.  Without REPS, one run sets the repetitions (about 0.3 s for
// the slowest query).  For a query that runs a benchmark algorithm the program also times the hand-written
// C and prints its own speed as a % of C's.
if (o.c && o.run) {
  const cp = require('child_process'), exe = path.resolve(o.c.replace(/\.c$/, '') + (o.c.endsWith('.c') ? '' : '.out'));
  try { cp.execFileSync(process.env.CC || 'cc', ['-O2', '-w', '-o', exe, o.c, '-lm'], { stdio: 'inherit' }); }
  catch (e) { console.error('cannot build ' + o.c + ' (set CC to a C compiler)'); process.exit(3); }
  let reps = o.run === true ? NaN : +o.run;
  if (!(reps >= 1)) {
    const once = cp.execFileSync(exe, ['-r', '1']).toString();
    const ms = Math.max(...[...once.matchAll(/^% steps .*?, ([0-9.]+) ms per run$/gm)].map(m => +m[1]), 1e-4);
    reps = Math.max(10, Math.min(1e6, Math.round(300 / ms)));
  }
  console.error('C: ' + exe + ' -r ' + reps);
  process.stdout.write(cp.execFileSync(exe, ['-r', String(reps)], { maxBuffer: 1 << 28 }).toString());
}
if (o.back) { const b = o.plain ? r.backPlain : r.backMnn; fs.writeFileSync(o.back, b.text); }
if (o.proof) fs.writeFileSync(o.proof, r.proof.text);
for (const x of r.runs) console.error((x.same ? 'same ' : 'DIFF ') + x.query + '  prolog ' + x.prolog.steps + ' steps' + (x.prolog.ms ? ' ' + x.prolog.ms.toFixed(3) + ' ms' : '') + ' | detlog ' + x.plain.steps + (x.plain.ms ? ' ' + x.plain.ms.toFixed(3) + ' ms' : '') + ' | mnn ' + x.mnn.steps + (x.mnn.ms ? ' ' + x.mnn.ms.toFixed(3) + ' ms' : ''));
if (r.sweep) console.error('growth: prolog ' + r.sweep.fit.prolog.label + ', detlog ' + r.sweep.fit.plain.label + ', mnn ' + r.sweep.fit.mnn.label);
console.error('proof: ' + (r.proof.ok ? 'ok' : r.proof.fails + ' failed') + ' (' + r.proof.checks.length + ' checks, ' + r.proof.warns + ' warnings)');
process.exit(r.proof.ok ? 0 : 2);
