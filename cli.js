#!/usr/bin/env node
// pl2detlog command line:  node cli.js prog.pl -q "fib(10, F)" [-q ...] [--plain] [--detlog out.pl] [--c out.c] [--back out.pl] [--proof proof.txt] [--stats]
const fs = require('fs'); const path = require('path');
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'backconv', 'cgen', 'proof', 'stats']) require('./src/' + f + '.js');
const P = globalThis.PL2D;
P.C_RUNTIME = fs.readFileSync(path.join(__dirname, 'src/runtime.c'), 'utf8');
const args = process.argv.slice(2); const qs = []; const o = {};
for (let i = 0; i < args.length; i++) {
  const a = args[i];
  if (a === '-q' || a === '--query') qs.push(args[++i]);
  else if (a.startsWith('--')) o[a.slice(2)] = (args[i + 1] && !args[i + 1].startsWith('-')) ? args[++i] : true;
  else o.file = a;
}
if (!o.file) { console.log('usage: node cli.js prog.pl -q QUERY [-q QUERY...] [--plain] [--detlog OUT.pl] [--c OUT.c] [--back OUT.pl] [--proof OUT.txt] [--stats] [--sweep TEMPLATE --values 1..10]'); process.exit(1); }
const src = fs.readFileSync(o.file, 'utf8');
const r = P.analyse(src, qs, { timing: !!o.stats, sweep: o.sweep ? { template: o.sweep, values: o.values || '1..10' } : null });
if (r.errors.length) console.error(r.errors.join('\n'));
const conv = o.plain ? r.plain : r.mnn;
const rt = fs.readFileSync(path.join(__dirname, 'src/detlog_runtime.pl'), 'utf8');
if (o.detlog) fs.writeFileSync(o.detlog, ':- style_check(-singleton).\n' + rt + '\n' + conv.text);
else if (!o.c && !o.back && !o.proof && !o.stats) process.stdout.write(conv.text);
if (o.c) fs.writeFileSync(o.c, P.toC(conv.text, { queries: conv.queries }).code);
if (o.back) { const b = o.plain ? r.backPlain : r.backMnn; fs.writeFileSync(o.back, b.text); }
if (o.proof) fs.writeFileSync(o.proof, r.proof.text);
for (const x of r.runs) console.error((x.same ? 'same ' : 'DIFF ') + x.query + '  prolog ' + x.prolog.steps + ' steps' + (x.prolog.ms ? ' ' + x.prolog.ms.toFixed(3) + ' ms' : '') + ' | detlog ' + x.plain.steps + (x.plain.ms ? ' ' + x.plain.ms.toFixed(3) + ' ms' : '') + ' | mnn ' + x.mnn.steps + (x.mnn.ms ? ' ' + x.mnn.ms.toFixed(3) + ' ms' : ''));
if (r.sweep) console.error('growth: prolog ' + r.sweep.fit.prolog.label + ', detlog ' + r.sweep.fit.plain.label + ', mnn ' + r.sweep.fit.mnn.label);
console.error('proof: ' + (r.proof.ok ? 'ok' : r.proof.fails + ' failed') + ' (' + r.proof.checks.length + ' checks, ' + r.proof.warns + ' warnings)');
process.exit(r.proof.ok ? 0 : 2);
