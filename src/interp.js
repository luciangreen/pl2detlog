/* interp.js - the pl2detlog interpreter: runs SWI-Prolog programs (and swipl command lines) on the
   fastest exact route, so that a program needs no SWI-Prolog, and runs faster where it has one.

   For each goal it has these routes:
     C        pl2detlog's C export, compiled by a C compiler where the host has one (nativeC, in
              Node) and run as a process; in a web page, the same analysis compiled to JavaScript
              (the native tier). Exact for calls that meet the type contract (ground inputs, fresh
              outputs); its answers must equal the MNN route's on the first run.
     MNN      the proved Detlog MNN rewrite (src/convert.js, src/rewrite.js), run by the JIT.
     Prolog   the reference engine with SWI-Prolog's library (src/swi.js): for what the conversion
              can't keep exact (database updates, files and streams, conversion errors, a round
              trip that reports a change), and whenever it is faster.
   The first run of a goal times the routes that apply, checks they agree, and keeps the fastest;
   the choice and the conversion are kept in a store (cache) so that the next process starts there.
   Where the store holds text (the conversion, the choice), it is kept as thermodynamic compression
   MNN codes (src/thermo.js) when that is smaller and decoding it is not slower than redoing the
   conversion; otherwise as plain JSON.

   Point 1 (a bound output is computed, then unified) and the rest of the hybrid's rules follow the
   Detlog MNN hybrid (github.com/luciangreen/detlogmnn, web/lib/hybrid.js).

   swipl command lines (runArgs): files are consulted (consult/include/use_module/ensure_loaded of
   files are read in; library modules are built in), load directives run, initialization/1 goals run
   after loading, -g goals run in order, initialization(main, main) runs and halts, and the exit code
   is SWI-Prolog's (1 when a goal fails, 2 when it raises an error, halt(N) gives N). A program that
   needs what only SWI-Prolog has (term or goal expansion, modules' private predicates, foreign
   libraries) is reported as such, so that a host with swipl can hand it over (needsSwi). */
(function (P) {
  'use strict';
  const D = (t) => P.deref(t);
  const VERSION = 'pl2detlog-interp-1';

  // ---------------------------------------------------------------- hashing (store keys)
  function hash(s) {
    let h1 = 0x811c9dc5, h2 = 0x01000193 ^ s.length;
    for (let i = 0; i < s.length; i++) { const c = s.charCodeAt(i); h1 = Math.imul(h1 ^ c, 16777619); h2 = Math.imul(h2 ^ c, 2246822519) ^ (h2 >>> 13); }
    return (h1 >>> 0).toString(16).padStart(8, '0') + (h2 >>> 0).toString(16).padStart(8, '0');
  }

  // ---------------------------------------------------------------- terms
  const conjList = (g) => { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? conjList(g.a[0]).concat(conjList(g.a[1])) : [g]; };
  const occurs = (v, t) => { t = D(t); return t === v || t.t === 'c' && t.a.some((x) => occurs(v, x)); };
  const keyOf = (g) => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };
  const isIte = (g) => { g = D(g); return g.t === 'c' && g.f === ';' && g.a.length === 2 && D(g.a[0]).t === 'c' && D(g.a[0]).f === '->' && D(g.a[0]).a.length === 2; };
  const isCut = (g) => { g = D(g); return g.t === 'a' && g.n === '!'; };

  // every predicate a goal can reach (subterms count, so goals inside findall/3 and call/N do)
  function reaches(prog, term) {
    const seen = new Set(), todo = [];
    const visit = (t) => { t = D(t); const k = keyOf(t); if (k && !seen.has(k)) { seen.add(k); if (prog.preds.has(k)) todo.push(k); } if (t.t === 'c') t.a.forEach(visit); };
    visit(term);
    while (todo.length) for (const cl of prog.preds.get(todo.pop())) visit(cl.body);
    return seen;
  }
  const DB = /^(assert[az]?|retract(all)?|abolish)\/\d+$/;
  // builtins whose effects only the Prolog route keeps: streams, files, the process, messages, state
  const EFFECTS = new Set(['open/3', 'open/4', 'close/1', 'close/2', 'read_line_to_string/2', 'read_line_to_codes/2', 'read_string/3', 'read_string/5', 'read_term/2', 'read_term/3', 'read/1', 'read/2',
    'read_file_to_string/3', 'read_file_to_codes/3', 'read_file_to_terms/3', 'json_read_dict/2', 'json_read_dict/3', 'json_read/2', 'json_write_dict/2', 'json_write_dict/3', 'json_write/2', 'json_write/3',
    'write/2', 'writeln/2', 'writeq/2', 'print/2', 'nl/1', 'tab/2', 'put_char/2', 'format/3', 'write_term/3', 'print_message/2', 'halt/0', 'halt/1', 'exists_file/1', 'exists_directory/1', 'directory_files/2',
    'delete_file/1', 'make_directory/1', 'working_directory/2', 'getenv/2', 'shell/1', 'shell/2', 'current_prolog_flag/2', 'absolute_file_name/2', 'absolute_file_name/3', 'get_char/1', 'get_char/2',
    'peek_char/2', 'get_code/2', 'at_end_of_stream/0', 'at_end_of_stream/1', 'consult/1', 'load_files/2', 'use_module/1', 'use_module/2', 'ensure_loaded/1', 'nb_setval/2', 'b_setval/2', 'nb_getval/2', 'b_getval/2',
    'clause/2', 'current_predicate/1', 'current_predicate/2', 'predicate_property/2', 'random/1', 'random_between/3', 'get_time/1', 'statistics/2', 'setarg/3', 'nb_setarg/3', 'tmp_file/2', 'time/1', 'prolog_load_context/2', 'stack_trace/0']);

  // builtins that look at variables themselves (identity, order, binding): the packets of the
  // compiled Detlog copy a call's arguments, so a call that compares variables it was given is kept
  // on the Prolog route (per call; a whole goal is compared with Prolog on its first run)
  const VARSENS = new Set(['==/2', '\\==/2', 'var/1', 'nonvar/1', '@</2', '@>/2', '@=</2', '@>=/2', 'compare/3', 'copy_term/2', 'term_variables/2', '=@=/2', '\\=@=/2', 'ground/1', 'sort/2', 'msort/2', 'sort/4', 'predsort/3', 'setof/3', 'bagof/3', 'unify_with_occurs_check/2', 'numbervars/3', 'numbervars/4', 'subsumes_term/2', 'term_to_atom/2', 'term_string/2', 'term_string/3', 'format/2', 'format/3', 'with_output_to/2', 'b_setval/2', 'b_getval/2', 'nb_getval/2', 'nb_setval/2', 'list_to_set/2', 'is_set/1', 'sort_unique/2', 'keysort/2']);

  // ---------------------------------------------------------------- point 1 (see detlogmnn)
  function steadfast(prog, k, i, assume = new Set()) {
    const id = k + '#' + i;
    if (assume.has(id)) return { ok: true, why: 'recursive call (proved by induction)' };
    const cls = prog.preds.get(k);
    if (!cls || !cls.length) return { ok: false, why: k + ' has no clauses here' };
    if (prog.dynamic.has(k)) return { ok: false, why: k + ' is dynamic' };
    const seen = new Set(assume).add(id), reasons = [];
    for (const [ci, cl] of cls.entries()) {
      const head = D(cl.head), V = D(head.a[i]);
      if (V.t !== 'v') return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ' has a value in argument ' + (i + 1) };
      if (head.a.some((x, j) => j !== i && occurs(V, x))) return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ' shares argument ' + (i + 1) + ' with another argument' };
      const r = bodyOk(prog, conjList(cl.body), V, seen);
      if (!r.ok) return { ok: false, why: 'clause ' + (ci + 1) + ' of ' + k + ': ' + r.why };
      reasons.push(r.why);
    }
    return { ok: true, why: [...new Set(reasons)].join('; ') };
  }
  function bodyOk(prog, goals, V, seen) {
    if (!goals.length) return { ok: false, why: 'the output is never computed' };
    const last = D(goals[goals.length - 1]);
    const cut = goals.map(isCut).lastIndexOf(true);
    if (cut >= 0) {
      if (goals.slice(0, cut).some((g) => occurs(V, g))) return { ok: false, why: 'the output is used before the cut' };
      const r = bodyOk(prog, goals.slice(cut + 1), V, seen);
      return r.ok ? { ok: true, why: 'cut first (D), then ' + r.why } : r;
    }
    if (goals.slice(0, -1).some((g) => occurs(V, g))) return { ok: false, why: 'the output is used before its value is computed' };
    if (last.t === 'c' && last.a.length === 2 && (last.f === '=' || last.f === 'is')) {
      const [l, r] = last.a.map(D);
      if (l === V && !occurs(V, r)) return { ok: true, why: 'computed then bound (A: ' + last.f + ')' };
      if (last.f === '=' && r === V && !occurs(V, l)) return { ok: true, why: 'computed then bound (A: =)' };
      return { ok: false, why: 'the output is compared, not just bound' };
    }
    if (isIte(last)) {
      const [c, t] = D(last.a[0]).a; const e = last.a[1];
      if (occurs(V, c)) return { ok: false, why: 'the output is used in a condition' };
      const rt = bodyOk(prog, conjList(t), V, seen); if (!rt.ok) return rt;
      const re = bodyOk(prog, conjList(e), V, seen); if (!re.ok) return re;
      return { ok: true, why: 'committed, then each branch bound (B)' };
    }
    const k = keyOf(last);
    if (k && prog.preds.has(k)) {
      const at = last.a.map(D).reduce((acc, x, j) => (x === V ? acc.concat([j]) : occurs(V, x) ? acc.concat([-1]) : acc), []);
      if (at.length !== 1 || at[0] < 0) return { ok: false, why: 'the output is passed to ' + k + ' other than as one whole argument' };
      const r = steadfast(prog, k, at[0], seen);
      return r.ok ? { ok: true, why: 'passed on (C: ' + k + ' argument ' + (at[0] + 1) + ')' } : { ok: false, why: r.why };
    }
    return { ok: false, why: k ? 'the last goal ' + k + ' is not a program predicate' : 'the last goal is not a call' };
  }
  function pointOne(prog, queryText) {
    const q = P.readTerm(queryText), g = D(q.term), k = keyOf(g);
    if (!k || g.t !== 'c' || !prog.preds.has(k)) return { text: queryText, outputs: [] };
    const args = g.a.map(D), outputs = [], parts = [], nm = P.namer();
    const shown = args.map((x) => P.show(x, { quoted: true, varName: (v) => { const f = q.vars.find(([, w]) => D(w) === v); return f ? f[0] : nm(v); } }));
    args.forEach((x, i) => {
      if (x.t === 'v' || !P.isGround(x)) return;
      const s = steadfast(prog, k, i); if (!s.ok) return;
      outputs.push({ arg: i + 1, why: s.why }); parts.push('_O' + (i + 1) + ' = ' + shown[i]); shown[i] = '_O' + (i + 1);
    });
    if (!outputs.length) return { text: queryText, outputs };
    return { text: P.show(P.Atom(g.f), { quoted: true }) + '(' + shown.join(', ') + '), ' + parts.join(', '), outputs };
  }

  // ---------------------------------------------------------------- loading SWI-Prolog files
  const LOADERS = new Set(['consult', 'include', 'ensure_loaded', 'use_module', 'load_files', 'reexport']);
  const DROP = new Set(['module', 'set_prolog_flag', 'license', 'encoding', 'style_check', 'use_foreign_library', 'meta_predicate', 'module_transparent', 'public', 'multifile', 'table', 'noprofile', 'create_prolog_flag', 'expects_dialect']);
  const NEEDS_SWI = new Set(['term_expansion/4', 'goal_expansion/4', 'prolog_load_file/2']);
  const fileSpec = (t) => { t = D(t); if (t.t === 'c' && t.f === 'library') return { library: true }; if (t.t === 'c' && t.a.length === 2 && t.f === ':') return fileSpec(t.a[1]); if (t.t === 'c' && t.f === '/' && t.a.length === 2) { const a = fileSpec(t.a[0]), b = fileSpec(t.a[1]); return { path: a.path + '/' + b.path }; } if (t.t === 'c' && t.a.length === 1) return { alias: t.f, path: P.textOf(t.a[0]) }; return { path: P.textOf(t) }; };
  const dirOf = (p) => { const i = p.lastIndexOf('/'); return i < 0 ? '' : i === 0 ? '/' : p.slice(0, i); };

  // The program text with every file it loads read in (each once), and what to run after loading.
  function loadFiles(io, files, opts = {}) {
    const st = { seen: new Set(), parts: [], loadGoals: [], init: [], initMain: null, needsSwi: [], missing: [], files: [] };
    for (const f of files) loadFile(io, f, st, io.cwd || '');
    st.src = st.parts.join('\n');
    if (opts.prelude !== false) st.src += '\n% ---- SWI-Prolog library (pl2detlog src/swi.js) ----\n' + P.SWI_PRELUDE;
    return st;
  }
  function findFile(io, base, name) {
    const cands = [];
    const p = P.joinPath(base, name);
    cands.push(p); if (!/\.\w+$/.test(name)) cands.push(p + '.pl', p + '.pro', p + '.prolog');
    for (const c of cands) { const s = io.stat ? io.stat(c) : (io.readFile(c) != null ? 'file' : null); if (s === 'file') return c; }
    return null;
  }
  // the text of a clause term, with its variables' names where the source gave them
  const clauseText = (t, vars) => {
    const names = new Map((vars || []).map(([n, v]) => [D(v), n])), nm = P.namer();
    const varName = (v) => names.get(v) || nm(v);
    t = D(t);
    return (t.t === 'c' && t.f === ':-' && t.a.length === 1 ? ':- ' + P.show(t.a[0], { quoted: true, varName, prec: 1199 }) + '.' : P.showClause(t, { varName })) + '\n';
  };
  const definesExpansion = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); while (t.t === 'c' && t.f === ':' && t.a.length === 2) t = D(t.a[1]); const k = keyOf(t); return k === 'term_expansion/2' || k === 'goal_expansion/2'; };
  // an engine on the program loaded so far, to run term_expansion/2 and goal_expansion/2 (Starlog's)
  function expander(io, st) {
    if (!st.hooks) return null;
    if (st.expander && st.expander.at === st.parts.length) return st.expander.e;
    let prog;
    try { prog = P.loadProgram(st.parts.join('\n') + '\n' + P.SWI_PRELUDE); } catch (e) { return null; }
    for (const [M, k] of st.privates || []) P.notePrivates(prog, M, [k]);
    prog.moduleFiles = new Map(st.moduleFiles || []);
    const e = new P.Engine(prog, { io, stepLimit: 1e8 });
    st.expander = { at: st.parts.length, e };
    return e;
  }
  function loadFile(io, path, st, base) {
    const full = findFile(io, base, path) || (io.cwd && base !== io.cwd ? findFile(io, io.cwd, path) : null);
    if (!full) { st.missing.push(path); return; }
    if (st.seen.has(full)) return;
    st.seen.add(full); st.files.push(full);
    const text = io.readFile(full);
    const dir = dirOf(full);
    // 1. read the clauses in order: operators and the files a clause loads take effect at once, so
    //    what follows is read with them (as SWI-Prolog reads a file)
    const items = []; let rest = text;
    for (;;) {
      const cl = P.nextClauseText(rest); if (cl === null) break;
      rest = rest.slice(cl.length);
      let r = null, err = null; try { r = P.readTerm(cl); } catch (e) { err = e; }
      const item = { text: cl, r, err };
      items.push(item);
      if (!r) continue;
      const t = D(r.term);
      if (!(t.t === 'c' && t.f === ':-' && t.a.length === 1)) continue;
      const d = D(t.a[0]), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
      P.applyOpDirective(d);
      if (d.t === 'c' && LOADERS.has(n)) {
        for (const x of (P.listToArray(d.a[0]) || [d.a[0]])) {
          const sp = fileSpec(x);
          if (sp.library || sp.alias && sp.alias !== 'library' && !findFile(io, dir, sp.path)) continue; // built in (src/swi.js)
          loadFile(io, sp.path, st, dir);
        }
        item.loaded = true;
      } else if (d.t === 'c' && d.f === '.') { for (const x of P.listToArray(d) || []) loadFile(io, fileSpec(x).path, st, dir); item.loaded = true; }
    }
    // 2. a module's predicates are renamed (src/swi.js)
    const md = (function () { for (const x of items) { if (!x.r) return null; const d = D(x.r.term); if (!(d.t === 'c' && d.f === ':-' && d.a.length === 1)) return null; const g = D(d.a[0]); if (g.t === 'c' && g.f === 'module' && g.a.length === 2) return g; } return null; })();
    const extra = [];
    if (md) {
      const M = P.textOf(md.a[0]);
      const ren = P.renameModule(items.map((x) => x.r ? x.r.term : P.Atom('true')), M, P.moduleExports(md));
      st.privates = (st.privates || []).concat(ren.privates.map((k) => [M, k]));
      (st.moduleFiles = st.moduleFiles || []).push([M, full]);
      items.forEach((x, i) => { if (x.r && !x.loaded) x.r = { term: D(ren.terms[i]), vars: x.r.vars, renamed: true }; });
      st.forwarded = st.forwarded || new Set();
      for (const fw of ren.forwarders) if (!st.forwarded.has(fw.key)) { st.forwarded.add(fw.key); extra.push({ text: P.showClause(fw.clause) + '\n', r: { term: fw.clause, vars: [], renamed: true } }); }
    }
    // 3. each clause, expanded by term_expansion/goal_expansion where the program has them, is kept
    st.parts.push('% ---- ' + full + ' ----');
    const defines = items.some((x) => x.r && definesExpansion(x.r.term));
    for (const item of items.concat(extra)) {
      if (!item.r) { st.parts.push(item.text); continue; }
      if (item.loaded) { st.parts.push('% ' + item.text.trim().replace(/\n/g, ' ')); continue; }
      let terms = [{ term: item.r.term, vars: item.r.vars, text: item.r.renamed ? null : item.text }];
      const ex = definesExpansion(item.r.term) ? null : expander(io, st);
      if (ex) {
        const out = P.expandClauses(ex, [{ term: item.r.term, vars: item.r.vars }]);
        if (out.length !== 1 || P.variantKey(out[0].term) !== P.variantKey(item.r.term)) terms = out.map((o) => ({ term: o.term, vars: o.vars, text: null }));
      }
      for (const { term, vars, text: tx } of terms) emit(io, st, term, tx || clauseText(term, vars), dir);
    }
    if (rest.trim()) st.parts.push(rest);
    if (defines) { st.hooks = true; st.expander = null; }
  }
  function emit(io, st, term, cl, dir) {
    const t = D(term);
    if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
      const d = D(t.a[0]), k = keyOf(d), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
      if (n === 'op') { st.parts.push(cl); return; }
      if (n === 'initialization') {
        const how = d.a.length === 2 ? P.textOf(d.a[1]) : 'now';
        if (how === 'main') st.initMain = P.show(d.a[0], { quoted: true }); else st.init.push(P.show(d.a[0], { quoted: true }));
        st.parts.push('% ' + cl.trim().replace(/\n/g, ' '));
        return;
      }
      if (DROP.has(n)) { st.parts.push('% ' + cl.trim().replace(/\n/g, ' ')); return; }
      if (n === 'dynamic' || n === 'discontiguous') { st.parts.push(cl); return; }
      if (n === 'begin_tests' || n === 'end_tests') { st.unit = n === 'begin_tests' ? P.textOf(d.a[0]) : null; st.parts.push('% ' + cl.trim().replace(/\n/g, ' ')); if (n === 'begin_tests' && d.a.length === 2) st.parts.push(P.show(P.Cmp('$plunit_unit', [d.a[0], d.a[1]]), { quoted: true, ignoreOps: false }) + '.'); return; }
      // any other directive runs when the files are loaded, in order
      st.loadGoals.push(P.show(d, { quoted: true }));
      st.parts.push('% ' + cl.trim().replace(/\n/g, ' '));
      if (k && /^(assert|retract)/.test(k)) st.dynamicLoad = true;
      return;
    }
    // plunit: test(Name) and test(Name, Options) between begin_tests(Unit) and end_tests(Unit)
    if (st.unit) {
      let h = t, b = P.Atom('true');
      if (t.t === 'c' && t.f === ':-' && t.a.length === 2) { h = D(t.a[0]); b = t.a[1]; }
      if (h.t === 'c' && (h.f === 'test' || /:test$/.test(h.f)) && (h.a.length === 1 || h.a.length === 2)) {
        const ut = P.Cmp(':-', [P.Cmp('$plunit_test', [P.Atom(st.unit), h.a[0], h.a.length === 2 ? h.a[1] : P.NIL, P.Int(++st.testSeq || (st.testSeq = 1))]), b]);
        st.parts.push(clauseText(ut, []));
        return;
      }
    }
    if (t.t === 'c' && t.f === ':-' && t.a.length === 2) { const hk = keyOf(t.a[0]); if (NEEDS_SWI.has(hk)) st.needsSwi.push('defines ' + hk); }
    else if (NEEDS_SWI.has(keyOf(t))) st.needsSwi.push('defines ' + keyOf(t));
    st.parts.push(cl);
  }

  // ---------------------------------------------------------------- the interpreter
  const sameAnswers = (a, b) => JSON.stringify(a.events) === JSON.stringify(b.events);
  function time(f, minMs = 20, maxReps = 50) { let reps = 0; const t0 = P.now(); let r; do { r = f(); reps++; } while (P.now() - t0 < minMs && reps < maxReps); return { r, ms: (P.now() - t0) / reps }; }
  function limit(steps, ms) {
    let n = 0, timedOut = false; const deadline = P.now() + ms;
    return { valueOf() { if ((++n & 4095) === 0 && P.now() > deadline) timedOut = true; return timedOut ? -1 : steps; }, toString() { return timedOut ? 'time limit ' + ms / 1000 + ' s' : String(steps); } };
  }
  const tidy = (e) => (e ? String(e).replace(/^step limit \(time limit ([\d.]+ s)\) exceeded$/, 'time limit ($1) exceeded') : e);
  // the events up to the first answer (a -g goal runs once)
  const firstOnly = (r) => { const ev = []; for (const e of r.events) { ev.push(e); if (e.k === 'row') break; } return Object.assign({}, r, { events: ev, answers: r.answers.slice(0, 1), output: ev.filter((e) => e.k === 'out').map((e) => e.text).join('') }); };

  // smallTerms(ts, n): the terms have at most n cells in all
  function smallTerms(ts, n) {
    const st = ts.slice();
    while (st.length) { const t = D(st.pop()); if (t.t === 'c') { if ((n -= t.a.length) < 0) return false; for (const x of t.a) st.push(x); } }
    return true;
  }

  // Prolog is kept for a goal when it takes this many times less than the Detlog MNN and C route
  const PROLOG_FASTER = 2, PROLOG_MIN_GAIN = 0.5;

  class Interpreter {
    // opts: io (see src/swi.js), store ({ get(key) -> string|null, set(key, string) }), nativeC (Node:
    // { compile(code) -> handle|null, run(handle, args) -> { stdout, stderr, status, ms } }),
    // stepLimit, timeLimitMs, checked
    constructor(opts = {}) {
      this.io = opts.io || P.defaultIO || {};
      this.store = opts.store || null; this.nativeC = opts.nativeC || null;
      this.stepLimit = opts.stepLimit || 5e7; this.timeLimitMs = opts.timeLimitMs || 60000; this.checked = !!opts.checked;
      this.log = opts.log || null; this.noAccel = !!opts.noAccel;
      this.setProgram('');
    }
    setProgram(src, meta = {}) {
      this.src = src; this.meta = meta; this.plans = new Map(); this.live = null; this.globals = new Map();
      this.srcKey = hash(VERSION + '\0' + src);
      const was = P.SWI_WRITE; P.SWI_WRITE = true;
      try { this.prog = this.freshProgram(); this.loadError = null; } catch (e) { this.prog = P.loadProgram(''); this.loadError = e.message; } finally { P.SWI_WRITE = was; }
      this.dynamic = !!meta.dynamicLoad || /\b(assert[az]?|retract(all)?|abolish)\s*\(/.test(src);
      if (this.installTime) this.installTime();
    }
    // the program as loaded, with its modules' private names and files (a run that changes the
    // database starts from a fresh copy)
    freshProgram() {
      const prog = P.loadProgram(this.src);
      for (const [M, k] of this.meta.privates || []) P.notePrivates(prog, M, [k]);
      prog.moduleFiles = new Map(this.meta.moduleFiles || []);
      return prog;
    }
    loadFiles(files, opts) { const st = loadFiles(this.io, files, opts); this.setProgram(st.src, st); return st; }

    // ---- the store
    remember(key, obj, reconvertMs) {
      if (!this.store) return;
      const json = JSON.stringify(obj);
      let rec = 'j' + json;
      try {
        const u8 = P.thermo.pack(json); const b64 = P.thermo.toBase64(u8);
        const t0 = P.now(); P.thermo.unpack(u8); const unpackMs = P.now() - t0;
        // thermo codes where they are smaller and decoding them is not slower than redoing the work
        if (b64.length + 1 < rec.length && unpackMs <= reconvertMs) rec = 't' + b64;
      } catch (e) { /* plain JSON */ }
      try { this.store.set(key, rec); } catch (e) { /* a full store keeps nothing */ }
    }
    recall(key) {
      if (!this.store) return null;
      let rec; try { rec = this.store.get(key); } catch (e) { return null; }
      if (!rec) return null;
      try { return JSON.parse(rec[0] === 't' ? P.thermo.unpack(P.thermo.fromBase64(rec.slice(1))) : rec.slice(1)); } catch (e) { return null; }
    }

    // ---- the plan for a goal: which routes apply and why
    plan(goalText) {
      goalText = goalText.trim().replace(/\.\s*$/, '');
      if (this.plans.has(goalText)) return this.plans.get(goalText);
      const plan = { goal: goalText, notes: [], key: this.srcKey + '-' + hash(goalText) };
      this.plans.set(goalText, plan);
      if (this.loadError) { plan.route = 'Prolog'; plan.why = 'the program has a syntax error: ' + this.loadError; return plan; }
      const saved = this.recall(plan.key);
      const t0 = P.now();
      const p1 = pointOne(this.prog, goalText);
      plan.runAs = p1.text;
      let reached = new Set();
      try { reached = reaches(this.prog, P.readTerm(p1.text).term); } catch (e) { plan.notes.push(e.message); }
      const effects = [...reached].filter((k) => DB.test(k) || EFFECTS.has(k) && !pureUses(this.prog, p1.text, k) || this.prog.dynamic.has(k));
      if (this.dynamic && [...reached].some((k) => this.prog.preds.has(k))) effects.push('the program changes its clauses as it loads');
      if (effects.length) { plan.route = 'Prolog'; plan.why = 'it uses ' + effects.slice(0, 4).join(', ') + ', whose effects only the Prolog route keeps'; return plan; }
      let conv = saved && saved.conv;
      if (!conv) {
        try { conv = P.convert(this.src, { mnn: true, s2a: false, queries: [p1.text] }); } catch (e) { plan.notes.push('conversion: ' + e.message); }
        if (conv && !conv.errors.length && conv.queries && conv.queries[0] && !conv.queries[0].error) {
          try {
            const back = P.backConvert(conv.text);
            const all = P.changeWarnings(this.src, back.text, back).filter((w) => reached.has(w.pred));
            const changes = all.filter((w) => w.kind === 'removed' || w.kind === 'error' || w.kind === 'added' && reached.has(w.pred));
            if (changes.length) conv = { changed: changes.map((c) => c.msg || String(c)) };
          } catch (e) { conv = { changed: ['back-conversion: ' + e.message] }; }
        }
      }
      if (!conv || conv.errors && conv.errors.length || !conv.queries || !conv.queries[0] || conv.queries[0].error) {
        plan.route = 'Prolog'; plan.why = conv && conv.changed ? 'the round trip back to Prolog reports a change' : 'the conversion has errors';
        if (conv && conv.errors) plan.notes.push(...conv.errors.map((x) => (x && x.msg ? (x.pred ? x.pred + ": " : "") + x.msg : String(x)))); if (conv && conv.changed) plan.notes.push(...conv.changed);
      } else {
        plan.conv = { text: conv.text, source: conv.source, queries: conv.queries.map((q) => ({ pred: q.pred, vars: q.vars, text: q.text })), errors: [] };
        plan.q = plan.conv.queries[0];
        plan.detlog = P.loadProgram(conv.text);
        try { plan.detlog.pairwiseSource = P.loadProgram(conv.source); } catch (e) { /* the JIT permutes in full */ }
      }
      plan.analysisMs = P.now() - t0;
      if (saved && saved.pick) { plan.pick = saved.pick; plan.why = saved.why; plan.timing = saved.timing; plan.fromStore = true; }
      return plan;
    }
    save(plan) {
      const obj = { v: VERSION, goal: plan.goal, pick: plan.pick, why: plan.why, timing: plan.timing };
      if (plan.conv) obj.conv = plan.conv;
      this.remember(plan.key, obj, plan.analysisMs || 0);
    }

    // ---- per call: inside the Prolog route, a call of a predicate whose every reachable clause
    // converted (and that reaches no effect the packet can't carry) can run on the compiled Detlog
    // MNN instead (the C route's JavaScript where its type contract holds, checked). Its first calls
    // run both ways: the answers (and output) must be the same, and the faster way is kept.
    prepareAccel() {
      if (this.acc !== undefined) return this.acc;
      this.acc = null;
      if (this.loadError || this.noAccel) return null;
      let conv; try { conv = P.convert(this.src, { mnn: true, s2a: false, queries: [], form: 'packets' }); } catch (e) { return null; }
      const bad = new Set(conv.errors.map((x) => x.pred).filter(Boolean));
      // the predicates the program may assert into: unknown targets turn per-call routes off
      const targets = new Set(); let anyTarget = false;
      for (const k of this.prog.order) for (const cl of this.prog.preds.get(k)) (function walk(t) { t = D(t); if (t.t !== 'c') return; if (DB.test(t.f + '/' + t.a.length)) { let h = D(t.a[0]); if (h.t === 'c' && h.f === ':-') h = D(h.a[0]); const hk = keyOf(h); if (hk && h.t !== 'v') targets.add(hk); else anyTarget = true; } t.a.forEach(walk); })(cl.body);
      if (anyTarget) return null;
      const ok = new Map();
      const pure = (k, stack = new Set()) => {
        if (ok.has(k)) return ok.get(k);
        if (stack.has(k)) return true;
        stack.add(k);
        let r = !bad.has(k) && !targets.has(k) && !this.prog.dynamic.has(k);
        if (r) for (const cl of this.prog.preds.get(k)) {
          const seen = new Set();
          (function walk(t) { t = D(t); const tk = keyOf(t); if (tk && !seen.has(tk)) { seen.add(tk); } if (t.t === 'c') t.a.forEach(walk); })(cl.body);
          for (const tk of seen) {
            if (DB.test(tk) || VARSENS.has(tk) || EFFECTS.has(tk) && !pureUses(this.prog, P.show(cl.body, { quoted: true }), tk)) { r = false; break; }
            if (this.prog.preds.has(tk) && tk !== k && !pure(tk, stack)) { r = false; break; }
          }
          if (!r) break;
        }
        stack.delete(k); ok.set(k, r); return r;
      };
      const keys = this.prog.order.filter((k) => this.prog.preds.get(k).length && !k.startsWith('$') && pure(k));
      if (!keys.length) return null;
      const was = [P.DETLOG_NATIVE, P.DETLOG_CHECKED];
      P.DETLOG_NATIVE = true; P.DETLOG_CHECKED = true; // the compiled program keeps the checked native tier
      let det;
      try { det = P.loadProgram(conv.text); P.detlogCall(det, keys[0].replace(/\/(\d+)$/, (m, n) => '__cp/' + (+n + 1)), [], {}); } catch (e) { /* compiled lazily */ }
      finally { [P.DETLOG_NATIVE, P.DETLOG_CHECKED] = was; }
      if (!det) return null;
      this.acc = { det, info: new Map(keys.map((k) => [k, { state: 'try', calls: 0, samples: 0, jitMs: 0, prologMs: 0, fails: 0 }])) };
      return this.acc;
    }
    // a sampled call's budget, on either route: more steps than this and the predicate stays on Prolog
    accelFn() {
      const SAMPLE_STEPS = 200000;
      const acc = this.prepareAccel(); if (!acc) return null;
      const self = this;
      return function (k, g, eng) {
        const info = acc.info.get(k); if (!info || info.state === 'prolog' || info.busy) return null;
        if (info.state === 'try' && ++info.calls < 20) return null; // only predicates called often are tried
        const n = g.t === 'c' ? g.a.length : 0, args = n ? g.a.slice() : [];
        // the compiled call copies its arguments (a packet's rows are copies): a call on a large term
        // (key(Clause, K) on a whole clause, say) stays on Prolog
        if (!smallTerms(args, 300)) return null;
        const R = P.Var('R');
        const call = (Rv) => {
          const was = [P.DETLOG_NATIVE, P.DETLOG_CHECKED]; P.DETLOG_NATIVE = true; P.DETLOG_CHECKED = true;
          try { return P.detlogCall(acc.det, k.replace(/\/(\d+)$/, (m, a) => '__cp/' + (+a + 1)), args.concat([Rv]), { stepLimit: info.state === 'try' ? SAMPLE_STEPS : 5e6 }); }
          catch (e) { return null; }
          finally { [P.DETLOG_NATIVE, P.DETLOG_CHECKED] = was; }
        };
        // the first call compiles: it is not timed
        if (info.state === 'try' && !info.warm) { info.warm = true; const W = P.Var('W'), m0 = eng.mark(); call(W); eng.undo(m0); }
        let t0 = P.now();
        const res = call(R);
        const jitMs = P.now() - t0;
        if (!res || !res.ok) { if (++info.fails > 2) info.state = 'prolog'; return null; }
        const items = P.listToArray(R) || [];
        // on the compiled route, calls 2, 4, 8, 16, .. are checked again (a few samples can miss a case)
        const recheck = info.state === 'jit' && ((info.jitCalls = (info.jitCalls || 0) + 1) & (info.jitCalls - 1)) === 0;
        if (info.state === 'try' || recheck) {
          // the same call on the Prolog route, all its answers, its output caught
          info.busy = true;
          // within a budget: a call with many answers (a search run under once/1, say) stays on Prolog
          const saveOut = eng.out, saveOn = eng.onOut, mark = eng.mark(), outer = eng.stepLimit; eng.out = ''; eng.onOut = null;
          const sols = []; let perr = null; t0 = P.now();
          eng.stepLimit = eng.steps + SAMPLE_STEPS;
          try { eng.solve(g, () => { sols.push({ out: eng.out, row: P.show(P.Cmp('e', args), { quoted: true, varName: P.namer() }) }); eng.out = ''; return true; }); } catch (e) { perr = e; }
          eng.stepLimit = outer;
          const prologMs = P.now() - t0, tail = eng.out;
          eng.out = saveOut; eng.onOut = saveOn; eng.undo(mark); info.busy = false;
          if (perr) { if (perr.halt) throw perr; if (perr instanceof P.LimitError) void (eng.steps > outer); info.state = 'prolog'; return null; }
          // the packet as the same events
          const mine = []; let pend = '';
          for (const it of items) { const x = D(it); if (x.t === 'c' && x.f === 'out') { pend += P.textOf(x.a[0]); continue; } const m2 = eng.mark(); const vals = P.listToArray(x.a[0]); let row = null; if (vals && vals.length === n && args.every((a, i) => eng.unify(a, vals[i]))) row = P.show(P.Cmp('e', args), { quoted: true, varName: P.namer() }); eng.undo(m2); if (row !== null) { mine.push({ out: pend, row }); pend = ''; } }
          const same = JSON.stringify(mine) === JSON.stringify(sols) && pend === tail;
          if (!same) { if (self.debugAccel) self.debugAccel(k, P.show(g, { quoted: true }), mine, sols, pend, tail); info.state = 'prolog'; if (self.log) self.log({ plan: { goal: k }, route: 'Prolog', why: 'per call: the compiled Detlog gave other answers' }); return null; }
          if (info.state === 'try') {
            info.jitMs += jitMs; info.prologMs += prologMs;
            if (++info.samples >= 3 && !self.debugAccel) info.state = info.jitMs < info.prologMs ? 'jit' : 'prolog';
          }
        }
        return (function* () {
          let rowsLeft = 0; for (const it of items) { const x = D(it); if (!(x.t === 'c' && x.f === 'out')) rowsLeft++; }
          for (let i = 0; i < items.length; i++) {
            const x = D(items[i]);
            if (x.t === 'c' && x.f === 'out') { eng.write(P.textOf(x.a[0])); continue; }
            rowsLeft--;
            const vals = P.listToArray(x.a[0]); const m = eng.mark();
            if (vals && vals.length === n && args.every((a, j) => eng.unify(a, vals[j]))) {
              const restOut = items.slice(i + 1).some((y) => { y = D(y); return y.t === 'c' && y.f === 'out'; });
              if (!rowsLeft && !restOut) { yield 'last'; return; }
              yield;
            }
            eng.undo(m);
          }
        })();
      };
    }

    // ---- the routes
    // stream: write output as it is made (to this.onOut/this.onErr), for the run whose effects count
    runProlog(text, stream) {
      // a program that changes its clauses keeps one live database for the whole session (as in
      // swipl: what initialization/1 or one goal asserts, the next goal sees)
      if ((this.dynamic || this.prog.dynamic.size) && !this.live) this.live = this.freshProgram();
      const prog = this.live || this.prog;
      const r = P.runQuery(prog, text, { stepLimit: limit(this.stepLimit, this.timeLimitMs), maxAnswers: 1, io: this.io, accel: this.accelFn(), globals: this.globals, onOut: stream ? this.onOut : null, onErr: stream ? this.onErr : null });
      r.error = tidy(r.error); if (stream && (this.onOut || this.onErr)) r.streamed = true; return r;
    }
    runDetlog(plan, native) {
      const was = P.DETLOG_NATIVE; P.DETLOG_NATIVE = native; P.DETLOG_CHECKED = this.checked;
      // a converted route works out every answer before giving one: a goal with endless answers reaches
      // this (smaller) limit there, and Prolog, which stops at the first answer, decides
      try { const r = P.runDetlogFast(plan.detlog, plan.q.pred, plan.q.vars, { stepLimit: limit(Math.min(this.stepLimit, this.convertedSteps || 3e6), Math.min(this.timeLimitMs, 5000)) }); r.error = tidy(r.error); return firstOnly(r); }
      finally { P.DETLOG_NATIVE = was; }
    }
    // the C export, compiled (Node): the answers between \x1e marks, the program's output around them
    runNativeC(plan) {
      if (!this.nativeC) return null;
      if (!plan.cHandle) {
        if (plan.cFailed) return null;
        const code = P.toC(plan.conv.text, { queries: plan.conv.queries, source: plan.conv.source, checked: this.checked, swiWrite: true }).code;
        plan.cHandle = this.nativeC.compile(code);
        if (!plan.cHandle) { plan.cFailed = true; return null; }
      }
      const r = this.nativeC.run(plan.cHandle, ['--events', '--first', '--no-ref']);
      if (!r || r.status !== 0) return { error: (r && r.stderr || 'the C program stopped').trim(), events: [], answers: [], output: '', ms: r && r.ms };
      const a = r.stdout.indexOf('\x1d'), b = r.stdout.lastIndexOf('\x1d');
      if (a < 0 || b <= a) return { error: 'the C program gave no answers', events: [], answers: [], output: '', ms: r.ms };
      const body = r.stdout.slice(a + 1, b), events = [], answers = [];
      const parts = body.split('\x1e');
      parts.forEach((p, i) => { if (i % 2 === 0) { if (p) events.push({ k: 'out', text: p }); } else { const text = p.replace(/\n$/, ''); events.push({ k: 'row', text }); answers.push({ text }); } });
      return { events, answers, output: events.filter((e) => e.k === 'out').map((e) => e.text).join(''), error: null, ms: r.ms };
    }

    // Runs a goal once (as swipl -g does). Returns { status: 'true'|'false'|'error'|'halt', code,
    // output, errOutput, error, route, why, answers, timing }
    run(goalText) {
      const was = P.SWI_WRITE; P.SWI_WRITE = true;
      try { return this._run(goalText); } finally { P.SWI_WRITE = was; }
    }
    _run(goalText) {
      const text = goalText.trim().replace(/\.\s*$/, '');
      const plan = this.plan(text);
      let res, route;
      if (plan.route === 'Prolog' || plan.pick === 'Prolog') { res = this.runProlog(text, true); route = 'Prolog'; }
      else if (plan.pick) {
        res = plan.pick === 'C' ? this.runNativeC(plan) : this.runDetlog(plan, plan.pick === 'C (JS)');
        route = plan.pick;
        if (!res) { res = this.runDetlog(plan, false); route = 'MNN'; }
      } else {
        // first run: one route, the intersection of Detlog MNN and C (the MNN program with its C tier;
        // compiled C on Node when the goal takes a while), checked once against Prolog. On the bundled
        // examples it is the fastest route or within 5% of it, and MNN alone is ~70x slower, so the
        // routes are no longer each timed.
        // (the C tier applies where the compiled program has native modes; it is known after a run)
        const m = time(() => this.runDetlog(plan, true), 0, 1);
        const nat = P.nativeModesOf(plan.detlog).length > 0;
        const limited = /limit/.test(m.r.error || '');
        const pr = limited ? null : time(() => this.runProlog(text), 0, 1);
        const own = nat ? 'C (JS)' : 'MNN';
        const timing = { mnn: nat ? null : m.ms, cjs: nat ? m.ms : null, prolog: pr ? pr.ms : null, c: null };
        const cands = [];
        const agrees = pr && !pr.r.error && !pr.r.halted && !pr.r.errOutput && sameAnswers(firstOnly(pr.r), m.r);
        if (!m.r.error && agrees) cands.push([own, m.ms, m.r]);
        if (this.nativeC && nat && m.ms >= (this.nativeC.minMs || 5) && cands.length) {
          const c = this.runNativeC(plan);
          if (c && !c.error && sameAnswers(c, m.r)) { timing.c = c.ms; cands.push(['C', c.ms, c]); }
          else if (c) plan.notes.push('compiled C: ' + (c.error || 'its answers differ from the MNN route\'s'));
        }
        plan.timing = timing;
        if (!cands.length) { plan.pick = 'Prolog'; plan.why = m.r.error ? 'the converted route raised ' + m.r.error + ': Prolog decides' : 'the routes disagree: Prolog decides'; res = this.runProlog(text, true); route = 'Prolog'; }
        else {
          cands.sort((x, y) => x[1] - y[1]);
          let [name, ms, r] = cands[0];
          plan.pick = name; plan.why = 'the Detlog MNN and C route, its answers checked against Prolog (' + cands.map(([n, t]) => n + ' ' + t.toFixed(3) + ' ms').join(', ') + ')';
          res = r; route = name;
          // Prolog when it is clearly faster (half the time or less). A first run includes compiling,
          // so when Prolog looks faster both are run once more, warm, and those times decide.
          // (cold times are rough, both ways: a first Prolog run also tries its per-call compiling)
          // A goal that takes long is timed well enough by its first runs; a short one is run twice more
          // each way. A goal under PROLOG_MIN_GAIN ms faster stays where it is (timer noise).
          if (pr.ms <= ms * 1.5 && ms - pr.ms >= PROLOG_MIN_GAIN / 2) {
            const best2 = (f) => { const a = time(f, 0, 1), b = time(f, 0, 1); return a.ms <= b.ms ? a : b; };
            const long = ms > 200;
            const warm = name === 'C' || long ? { ms } : best2(() => this.runDetlog(plan, nat));
            const pw = long ? pr : best2(() => this.runProlog(text));
            if (!pw.r.error && sameAnswers(firstOnly(pw.r), r) && pw.ms * PROLOG_FASTER <= warm.ms && warm.ms - pw.ms >= PROLOG_MIN_GAIN) {
              plan.pick = 'Prolog'; route = 'Prolog'; res = pw.r; timing.prolog = pw.ms; timing[name === 'C' ? 'c' : nat ? 'cjs' : 'mnn'] = warm.ms;
              plan.why = 'Prolog, at least ' + PROLOG_FASTER + 'x faster than the Detlog MNN and C route here (' + pw.ms.toFixed(3) + ' ms against ' + name + ' ' + warm.ms.toFixed(3) + ' ms)';
            }
          }
        }
        this.save(plan);
      }
      if (res.error && route !== 'Prolog') {
        // an error on a converted route: Prolog decides
        const pr = this.runProlog(text);
        if (!sameAnswers(firstOnly(pr), res) || pr.error !== res.error) { res = pr; route = 'Prolog'; }
      }
      if (route === 'Prolog') res = Object.assign(firstOnly(res), { errOutput: res.errOutput, halted: res.halted, error: res.error, streamed: res.streamed });
      const status = res.halted != null ? 'halt' : res.error ? 'error' : res.answers.length ? 'true' : 'false';
      return { status, code: res.halted, output: res.output || '', errOutput: res.errOutput || '', error: res.error || null, answers: res.answers.map((a) => a.text), route, why: plan.why, timing: plan.timing, plan, streamed: !!res.streamed };
    }

    // ---- swipl command lines
    // swipl [options] [file ...] [-- arg ...]: -g Goal (repeatable), -t Toplevel, -s File, -l File,
    // -q, -O, --stack-limit=..., file.pl; arguments after -- (or after the script) are the argv flag.
    static parseArgs(args) {
      const spec = { goals: [], toplevel: null, files: [], argv: [], quiet: false };
      let i = 0;
      for (; i < args.length; i++) {
        const a = args[i];
        if (a === '--') { i++; break; }
        if (a === '-g') spec.goals.push(args[++i]);
        else if (a === '-t') spec.toplevel = args[++i];
        else if (a === '-s' || a === '-l' || a === '-f' && args[i + 1] !== 'none') spec.files.push(args[++i]);
        else if (a === '-f') i++;
        else if (a === '-q' || a === '-O' || a === '--quiet' || a === '--traditional' || a === '--no-tty' || /^--(stack[-_]limit|table[-_]space|home|nosignals|no-signals|threads|pce|no-pce)/.test(a)) { if (a === '-q' || a === '--quiet') spec.quiet = true; }
        else if (/^-[a-zA-Z]/.test(a)) { /* other options: ignored */ }
        else { spec.files.push(a); if (/\.(pl|pro|prolog)$/.test(a) && !spec.goals.length) { i++; break; } }
      }
      spec.argv = args.slice(i);
      return spec;
    }
    // Runs a swipl command line. out(s)/err(s) receive the output. Returns the exit code.
    // stream: output is written as the goals make it (else after each goal)
    runArgs(args, { out = () => {}, err = () => {}, stream = false } = {}) {
      const spec = Interpreter.parseArgs(args);
      if (stream) { this.onOut = out; this.onErr = err; }
      this.io.argv = spec.argv;
      const st = this.loadFiles(spec.files);
      for (const f of st.missing) { err('Warning: source_sink `' + f + "' does not exist\n"); }
      if (this.loadError) { err('ERROR: ' + this.loadError + '\n'); }
      const goal = (g, kind) => {
        const r = this.run(g);
        if (this.log) this.log(r);
        if (!r.streamed) { out(r.output); if (r.errOutput) err(r.errOutput); }
        if (r.status === 'halt') return { halt: r.code };
        if (r.status === 'error') { err((kind === 'init' ? 'Warning: ' : 'Warning: ') + 'goal (' + g + ') raised exception:\n' + r.error + '\n'); return { code: 2, failed: true }; }
        if (r.status === 'false') { err('Warning: goal (' + g + ') failed\n'); return { code: 1, failed: true }; }
        return { code: 0 };
      };
      for (const g of st.loadGoals.concat(st.init)) { const r = goal(g, 'init'); if (r.halt != null) return r.halt; }
      if (st.initMain) { const r = goal(st.initMain, 'main'); if (r.halt != null) return r.halt; return r.failed ? 1 : 0; }
      for (const g of spec.goals) { const r = goal(g, 'goal'); if (r.halt != null) return r.halt; if (r.failed) return r.code; }
      if (spec.toplevel && spec.toplevel !== 'halt') { const r = goal(spec.toplevel, 'toplevel'); if (r.halt != null) return r.halt; return r.failed ? 1 : 0; }
      return 0;
    }
  }
  Interpreter.prototype.installTime = function () {
    const B = P.builtins; if (B['time/1'] && B['time/1'].interp) return;
    B['$time_start/1'] = { fn: (a, e) => e.unify(a[0], P.Cmp('t', [P.Num(P.now(), true), P.Int(e.steps)])) };
    B['$time_report/1'] = { fn: (a, e) => { const t = D(a[0]); const ms = P.now() - D(t.a[0]).v, n = e.steps - D(t.a[1]).v; const s = ms / 1000; e.writeErr('% ' + n.toLocaleString('en') + ' inferences, ' + s.toFixed(3) + ' CPU in ' + s.toFixed(3) + ' seconds (100% CPU, ' + (s > 0 ? Math.round(n / s).toLocaleString('en') : 'Infinite') + ' Lips)\n'); return true; } };
    B['time/1'] = { call: true, interp: true, fn: (a) => { const T = P.Var('T'), rep = P.Cmp('$time_report', [T]); return P.Cmp(',', [P.Cmp('$time_start', [T]), P.Cmp(';', [P.Cmp('*->', [P.Cmp('call', [a[0]]), rep]), P.Cmp(',', [rep, P.Atom('fail')])])]); } };
  };

  // Is every use of builtin k that a goal reaches free of effects? format/3 to atom(A), string(S),
  // codes(C) or chars(C) only builds text; current_prolog_flag/2 for a flag other than argv is a constant.
  const SINKS = new Set(['atom', 'string', 'codes', 'chars']);
  function pureUses(prog, goalText, k) {
    if (k !== 'format/3' && k !== 'current_prolog_flag/2') return false;
    let t; try { t = P.readTerm(goalText).term; } catch (e) { return false; }
    const seen = new Set(); let pure = true;
    const visit = (x) => {
      x = D(x); if (!pure) return; const xk = keyOf(x);
      if (xk === k) { const a0 = D(x.a[0]); if (k === 'format/3' ? !(a0.t === 'c' && a0.a.length === 1 && SINKS.has(a0.f)) : !(a0.t === 'a' && a0.n !== 'argv')) { pure = false; return; } }
      if (xk && prog.preds.has(xk) && !seen.has(xk)) { seen.add(xk); for (const cl of prog.preds.get(xk)) visit(cl.body); }
      if (x.t === 'c') x.a.forEach(visit);
    };
    visit(t);
    return pure;
  }

  // the predicates a goal can call that are neither in the program nor built in
  function unknown(prog, goalText) {
    let t; try { t = P.readTerm(goalText).term; } catch (e) { return []; }
    const r = reaches(prog, t), out = [];
    // a program that loads files while it runs defines predicates only then: nothing is known missing
    if (['consult/1', 'use_module/1', 'use_module/2', 'load_files/2', 'ensure_loaded/1'].some((k) => r.has(k))) return [];
    for (const k of r) {
      if (prog.preds.has(k) || P.builtins[k] || P.CONTROL.has(k) || prog.dynamic.has(k)) continue;
      if (/^call\/\d+$/.test(k) || k === ':/2' || /^'?\$/.test(k)) continue;
      // only goals: a key found in data (an atom or a compound used as a value) may not be called at all
      out.push(k);
    }
    return out.filter((k) => calledSomewhere(prog, t, k));
  }
  // is k in goal position somewhere the goal can reach (bodies, and the meta-arguments of control)?
  function calledSomewhere(prog, top, k) {
    const seen = new Set();
    const META = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'not/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'catch/3': [0, 2], 'with_output_to/2': [1], 'time/1': [0], '^/2': [1], '$scc/3': [0, 1, 2], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1] };
    let found = false;
    const goal = (g) => {
      g = D(g); if (found) return; const gk = keyOf(g); if (!gk) return;
      if (gk === k) { found = true; return; }
      if (META[gk]) { for (const i of META[gk]) goal(g.a[i]); return; }
      if (prog.preds.has(gk) && !seen.has(gk)) { seen.add(gk); for (const cl of prog.preds.get(gk)) goal(cl.body); }
    };
    goal(top);
    return found;
  }

  P.Interpreter = Interpreter;
  P.interp = { loadFiles, unknown, reaches, steadfast, pointOne, hash, VERSION, EFFECTS };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
