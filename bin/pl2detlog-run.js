#!/usr/bin/env node
// pl2detlog-run: runs a swipl command line on the pl2detlog interpreter (src/interp.js).
//
//   pl2detlog-run [swipl options] [file.pl ...] [-- args]     as  swipl ...
//   e.g.  pl2detlog-run -g main -t halt proofs/updates.pl
//
// Each goal runs on the fastest exact route: compiled C (with the C compiler on PATH, or $CC), the
// C route's JavaScript, Detlog MNN or Prolog. Choices, conversions and compiled programs are kept in
// $PL2DETLOG_CACHE (default ~/.cache/pl2detlog), the text ones as thermodynamic compression codes
// where that is smaller and not slower. A program that needs what only SWI-Prolog has is handed to
// swipl when it is installed (unless --no-swipl), with the same arguments.
//
// Options of its own (before the swipl ones): --explain (the route of each goal, to stderr),
// --no-swipl, --no-c (no compiled C), --checked (the C route tests its type contract).
'use strict';
const fs = require('fs'), path = require('path'), os = require('os'), cp = require('child_process');

const LIB = [path.join(__dirname, '..', 'dist', 'pl2detlog.js'), path.join(__dirname, 'pl2detlog.js')].find((f) => fs.existsSync(f));
if (!globalThis.PL2D) require(LIB);
const P = globalThis.PL2D;

let args = process.argv.slice(2);
const own = new Set();
while (args.length && ['--explain', '--no-swipl', '--no-c', '--checked'].includes(args[0])) own.add(args.shift());
const env = process.env;
const explain = own.has('--explain') || env.PL2DETLOG_EXPLAIN === '1';

// ---- the file system and the process, for the engine
const io = {
  cwd: process.cwd(), root: '/', env,
  readFile: (p) => { try { return fs.readFileSync(p, 'utf8'); } catch (e) { return null; } },
  writeFile: (p, s, append) => { if (append) fs.appendFileSync(p, s); else fs.writeFileSync(p, s); },
  stat: (p) => { try { const s = fs.statSync(p); return s.isDirectory() ? 'dir' : 'file'; } catch (e) { return null; } },
  list: (p) => { try { return fs.readdirSync(p); } catch (e) { return null; } },
  deleteFile: (p) => fs.unlinkSync(p),
  mkdir: (p) => fs.mkdirSync(p),
  rename: (a, b) => fs.renameSync(a, b),
  tmpDir: os.tmpdir(),
  shell: (cmd) => { const r = cp.spawnSync('/bin/sh', ['-c', cmd], { stdio: 'inherit' }); return r.status ?? 1; },
  readStdin: () => { const b = Buffer.alloc(65536); let n; try { n = fs.readSync(0, b, 0, b.length, null); } catch (e) { if (e.code === 'EAGAIN') return ''; return null; } return n ? b.slice(0, n).toString('utf8') : null; }
};

// ---- the store: one file per key
const cacheDir = env.PL2DETLOG_CACHE || path.join(os.homedir() || os.tmpdir(), '.cache', 'pl2detlog');
try { fs.mkdirSync(cacheDir, { recursive: true }); } catch (e) { /* no store */ }
const store = {
  get: (k) => { try { return fs.readFileSync(path.join(cacheDir, k + '.plan'), 'utf8'); } catch (e) { return null; } },
  set: (k, v) => { try { fs.writeFileSync(path.join(cacheDir, k + '.plan'), v); } catch (e) { /* not kept */ } }
};

// ---- compiled C
function which(cmd) { for (const d of (env.PATH || '').split(path.delimiter)) { const f = path.join(d, cmd); try { fs.accessSync(f, fs.constants.X_OK); return f; } catch (e) { /* next */ } } return null; }
const cc = own.has('--no-c') ? null : env.CC ? which(env.CC) || env.CC : which('cc') || which('gcc') || which('clang');
const nativeC = cc && {
  minMs: Number(env.PL2DETLOG_C_MIN_MS || 5),
  compile(code) {
    const key = P.interp.hash(code + '\0' + cc);
    const bin = path.join(cacheDir, key + (process.platform === 'win32' ? '.exe' : '.bin'));
    if (fs.existsSync(bin)) return bin;
    const src = path.join(cacheDir, key + '.c');
    fs.writeFileSync(src, code);
    const r = cp.spawnSync(cc, ['-O2', '-w', '-o', bin, src, '-lm'], { encoding: 'utf8' });
    try { fs.unlinkSync(src); } catch (e) { /* gone */ }
    return r.status === 0 ? bin : null;
  },
  run(bin, a) {
    const t0 = process.hrtime.bigint();
    const r = cp.spawnSync(bin, a, { encoding: 'utf8', maxBuffer: 1 << 28 });
    return { stdout: r.stdout || '', stderr: r.stderr || '', status: r.status, ms: Number(process.hrtime.bigint() - t0) / 1e6 };
  }
};

// ---- swipl, for programs that need it
const swipl = own.has('--no-swipl') ? null : which('swipl');
function handOver(why) {
  if (explain) process.stderr.write('% pl2detlog: handing over to swipl (' + why + ')\n');
  const r = cp.spawnSync(swipl, args, { stdio: 'inherit' });
  process.exit(r.status ?? 1);
}

const it = new P.Interpreter({ io, store, nativeC, noAccel: env.PL2DETLOG_NO_ACCEL === '1', checked: own.has('--checked'), log: explain ? (r) => process.stderr.write('% ' + r.plan.goal + ': ' + r.route + (r.why ? ' (' + r.why + ')' : '') + '\n') : null });
// a program that needs SWI-Prolog: checked before anything runs, so nothing happens twice
if (swipl) {
  const spec = P.Interpreter.parseArgs(args);
  const st = P.interp.loadFiles(io, spec.files);
  const needs = st.needsSwi.slice();
  it.setProgram(st.src, st);
  if (it.loadError) needs.push('syntax: ' + it.loadError);
  const goals = spec.goals.concat(st.loadGoals, st.init, st.initMain ? [st.initMain] : [], spec.toplevel && spec.toplevel !== 'halt' ? [spec.toplevel] : []);
  for (const g of goals) { const u = P.interp.unknown(it.prog, g); if (u.length) needs.push('unknown ' + u.slice(0, 3).join(', ')); }
  if (needs.length) handOver(needs.join('; '));
}
const code = it.runArgs(args, { out: (s) => s && process.stdout.write(s), err: (s) => s && process.stderr.write(s) });
process.exitCode = code;
