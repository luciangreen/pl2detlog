/* pl2detlog C generator: Detlog -> C.  One C function per Detlog predicate selects the clause
   by its first argument and commits to it (no choicepoint); if_commit/3 becomes a trail mark,
   the condition, and an undo before the else branch. */
(function (P) {
  'use strict';
  const { deref, listToArray, show } = P;
  const D = deref;
  const RT = { // Detlog runtime predicate -> C function
    'rows_concat/2': 'rt_rows_concat', 'splice_extend/4': 'rt_splice_extend', 'project_rows/4': 'rt_project_rows', 'project_list/4': 'rt_project_list',
    'packet_first/3': 'rt_packet_first', 'packet_split/3': 'rt_packet_split', 'effect_text/2': 'rt_effect_text', 'builtin_rows/2': 'rt_builtin_rows',
    'cp_filter/3': 'rt_cp_filter', 'aggregate_list/3': 'rt_aggregate_list', 'splice_safe/2': 'rt_splice_safe', 'splice2/6': 'rt_splice2',
    'memo_lookup/3': 'rt_memo_lookup', 'rows_concat_cut/2': 'rt_rows_concat_cut', 'rows_cut_concat/2': 'rt_rows_cut_concat', 'strip_cut/2': 'rt_strip_cut', 'cut_in/2': 'rt_cut_in', 'memo_store/3': 'rt_memo_store', 's2a_rows/3': 'rt_s2a_rows'
  };
  const C_BUILTINS = new Set(['=/2', '\\=/2', '==/2', '\\==/2', '@</2', '@>/2', '@=</2', '@>=/2', 'compare/3', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2',
    'true/0', 'fail/0', 'false/0', 'var/1', 'nonvar/1', 'atom/1', 'number/1', 'integer/1', 'float/1', 'atomic/1', 'compound/1', 'callable/1', 'string/1', 'is_list/1', 'ground/1',
    'copy_term/2', 'functor/3', 'arg/3', '=../2', 'succ/2', 'plus/3', 'length/2', 'reverse/2', 'msort/2', 'sort/2', 'sum_list/2', 'sumlist/2', 'max_list/2', 'min_list/2',
    'nth0/3', 'nth1/3', 'last/2', 'memberchk/2', 'numlist/3', 'atom_length/2', 'string_length/2', 'atom_codes/2', 'atom_chars/2', 'string_codes/2', 'string_chars/2',
    'char_code/2', 'atom_number/2', 'number_codes/2', 'atom_string/2', 'string_concat/3', 'atomic_list_concat/2', 'atomic_list_concat/3', 'upcase_atom/2', 'downcase_atom/2',
    'term_to_atom/2', 'throw/1', 'code_type/2', 'split_string/4']);
  const C_ROWS = new Set(['permutation/2', 'atom_concat/3', 'char_type/2', 'member/2', 'between/3', 'append/3', 'select/3', 'nth0/3', 'nth1/3', 'length/2', 'last/2', 'arg/3']);
  const C_EFFECTS = new Set(['write/1', 'print/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'writeln/1', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'format/3', 'flush_output/0']);

  function mangle(s) { return s.replace(/[^A-Za-z0-9_]/g, c => '_' + c.charCodeAt(0).toString(16).toUpperCase().padStart(2, '0')); }
  function cstr(s) {
    let o = '"';
    for (const ch of Buffer_from(s)) {
      if (ch === 34) o += '\\"'; else if (ch === 92) o += '\\\\'; else if (ch === 10) o += '\\n'; else if (ch === 9) o += '\\t'; else if (ch === 13) o += '\\r';
      else if (ch < 32 || ch === 127) o += '\\' + ch.toString(8).padStart(3, '0');
      else if (ch === 63) o += '\\?';
      else o += String.fromCharCode(ch);
    }
    return o + '"';
  }
  // UTF-8 bytes (works in browsers and node)
  function Buffer_from(s) { const bytes = []; const enc = typeof TextEncoder !== 'undefined' ? new TextEncoder().encode(s) : null; if (enc) { for (const b of enc) bytes.push(b); return bytes; } for (const c of unescape(encodeURIComponent(s))) bytes.push(c.charCodeAt(0)); return bytes; }
  // strings in C source must stay byte strings: emit non-ASCII bytes as octal escapes
  function cstrBytes(s) { let o = '"'; for (const b of Buffer_from(s)) { if (b === 34) o += '\\"'; else if (b === 92) o += '\\\\'; else if (b === 10) o += '\\n'; else if (b === 9) o += '\\t'; else if (b < 32 || b >= 127 || b === 63) o += '\\' + b.toString(8).padStart(3, '0'); else o += String.fromCharCode(b); } return o + '"'; }

  function toC(detlogText, opts) {
    opts = opts || {};
    const prog = P.loadProgram(detlogText);
    const warnings = []; const warned = new Set();
    const warn = m => { if (!warned.has(m)) { warned.add(m); warnings.push(m); } };
    const atoms = new Map(), fns = new Map();
    const atomIx = n => { if (!atoms.has(n)) atoms.set(n, atoms.size); return 'AT[' + atoms.get(n) + ']'; };
    const fnIx = n => { if (!fns.has(n)) fns.set(n, fns.size); return 'FN[' + fns.get(n) + ']'; };
    const pfn = k => 'p_' + mangle(k.replace('/', '_'));
    let uid = 0;
    const defs = [], protos = [];

    function termC(t, vm) {
      t = D(t);
      switch (t.t) {
        case 'v': { if (!t.name || t.name === '_') return 'mk_var()'; const v = vm.get(t); if (!v) throw new Error('unknown variable ' + t.name); return v; }
        case 'n': return t.f ? 'mk_flt(' + (Number.isFinite(t.v) ? String(t.v) + (/[.e]/i.test(String(t.v)) ? '' : '.0') : (t.v > 0 ? 'INFINITY' : t.v < 0 ? '-INFINITY' : 'NAN')) + ')' : 'mk_int(' + t.v + 'LL)';
        case 'a': return atomIx(t.n);
        case 's': return 'mk_str(' + cstrBytes(t.v) + ')';
        case 'c': {
          if (t.f === '.' && t.a.length === 2) {
            const items = []; let x = t;
            while (x.t === 'c' && x.f === '.' && x.a.length === 2) { items.push(termC(x.a[0], vm)); x = D(x.a[1]); }
            return 'mk_list(' + items.length + ', (Term*[]){' + items.join(', ') + '}, ' + termC(x, vm) + ')';
          }
          return 'mk_cmp(' + fnIx(t.f) + ', ' + t.a.length + ', (Term*[]){' + t.a.map(x => termC(x, vm)).join(', ') + '})';
        }
      }
      throw new Error('bad term');
    }
    function argsC(as, vm) { return as.length ? '(Term*[]){' + as.map(x => termC(x, vm)).join(', ') + '}' : 'NULL'; }
    function stmt(g, vm, fail, ind) {
      g = D(g); const k = P.key(g); const as = g.t === 'c' ? g.a : [];
      if (g.t === 'v') throw new Error('variable goal');
      switch (k) {
        case ',/2': return stmt(g.a[0], vm, fail, ind) + stmt(g.a[1], vm, fail, ind);
        case 'true/0': return '';
        case 'fail/0': case 'false/0': return ind + fail + '\n';
        case 'if_commit/3': {
          const n = ++uid;
          return ind + '{ size_t m' + n + ' = TR_TOP; int ok' + n + ' = 1; dl_decisions++;\n' +
            ind + '  do {\n' + stmt(g.a[0], vm, '{ ok' + n + ' = 0; break; }', ind + '    ') + ind + '  } while (0);\n' +
            ind + '  if (ok' + n + ') {\n' + stmt(g.a[1], vm, fail, ind + '    ') + ind + '  } else {\n' + ind + '    undo(m' + n + ');\n' + stmt(g.a[2], vm, fail, ind + '    ') + ind + '  }\n' + ind + '}\n';
        }
        case 'detlog_unsupported/2': warn('predicate ' + show(g.a[0]) + ' was not converted; calling it stops the C program');
          return ind + 'rt_unsupported(' + cstrBytes(show(g.a[0])) + ');\n';
      }
      if (RT[k]) {
        if (k === 'builtin_rows/2') { const bk = P.key(g.a[0]); if (!C_ROWS.has(bk)) warn('builtin_rows for ' + bk + ' is not in the C runtime'); }
        if (k === 'effect_text/2') { const bk = P.key(g.a[0]); if (!C_EFFECTS.has(bk)) warn('output builtin ' + bk + ' is not in the C runtime'); }
        return ind + 'if (!' + RT[k] + '(' + as.map(x => termC(x, vm)).join(', ') + ')) ' + fail + '\n';
      }
      if (prog.preds.has(k)) return ind + 'if (!' + pfn(k) + '(' + argsC(as, vm) + ')) ' + fail + '\n';
      if (!C_BUILTINS.has(k)) warn('builtin ' + k + ' is not in the C runtime');
      return ind + 'if (!bi_call(' + cstrBytes(k) + ', ' + argsC(as, vm) + ')) ' + fail + '\n';
    }
    function headInfo(t) {
      t = D(t);
      if (t.t === 'v') return '-1, NULL, 0, 0';
      if (t.t === 'a') return 'T_ATOM, ' + atomIx(t.n) + '->name, 0, 0';
      if (t.t === 'n') return t.f ? 'T_FLT, NULL, 0, 0' : 'T_INT, NULL, 0, ' + t.v + 'LL';
      if (t.t === 's') return 'T_STR, NULL, 0, 0';
      return 'T_CMP, ' + fnIx(t.f) + ', ' + t.a.length + ', 0';
    }
    for (const k of prog.order) {
      const cls = prog.preds.get(k); const f = pfn(k);
      protos.push('static int ' + f + '(Term **a);');
      const parts = [];
      cls.forEach((cl, i) => {
        const vm = new Map(); let vi = 0;
        const vs = P.termVars(P.Cmp('-', [cl.head, cl.body])).filter(v => v.name && v.name !== '_');
        for (const v of vs) vm.set(v, 'v' + (++vi));
        const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
        let body = 'static int ' + f + '_c' + (i + 1) + '(Term **a) {\n';
        if (vs.length) body += '  Term ' + vs.map(v => '*' + vm.get(v) + ' = mk_var()').join(', ') + ';\n';
        body += '  (void)a;\n';
        hargs.forEach((h, j) => { body += '  if (!unify(a[' + j + '], ' + termC(h, vm) + ')) return 0;\n'; });
        body += stmt(cl.body, vm, 'return -1;', '  ');
        body += '  return 1;\n}\n';
        defs.push(body);
        parts.push({ i, info: hargs.length ? headInfo(hargs[0]) : '-1, NULL, 0, 0' });
      });
      let disp = 'static int ' + f + '(Term **a) {\n  STEP(); size_t m = TR_TOP; int r; (void)m; (void)r;\n';
      for (const p of parts) {
        const test = (D(cls[0].head).t === 'c') ? 'fa(a[0], ' + p.info + ')' : '1';
        disp += '  if (' + test + ') { r = ' + f + '_c' + (p.i + 1) + '(a); if (r == 1) return 1; undo(m); if (r < 0) return 0; }\n';
      }
      disp += '  return 0;\n}\n';
      defs.push(disp);
    }
    // main
    const qs = (opts.queries || []).filter(q => q.pred && prog.preds.has(q.pred + '__cp/' + (q.vars.length + 1)));
    let main = 'int main(int argc, char **argv) {\n  int reps = 1; if (argc > 2 && !strcmp(argv[1], "-r")) reps = atoi(argv[2]); if (reps < 1) reps = 1;\n  rt_init(); init_tables();\n';
    qs.forEach(q => {
      const k = q.pred + '__cp/' + (q.vars.length + 1);
      main += '  {\n    const char *nm[] = {' + (q.vars.length ? q.vars.map(cstrBytes).join(', ') : '""') + '};\n';
      main += '    Term *qv[' + (q.vars.length + 1) + ']; int ok = 0; long s0 = dl_steps, d0 = dl_decisions; double t0 = now_ms();\n';
      main += '    for (int rep = 0; rep < reps; rep++) { for (int i = 0; i < ' + (q.vars.length + 1) + '; i++) qv[i] = mk_var(); memset(memo, 0, sizeof memo); ok = ' + pfn(k) + '(qv); }\n';
      main += '    double t1 = now_ms();\n';
      main += '    printf("?- %s.\\n", ' + cstrBytes(q.text) + ');\n';
      main += '    if (!ok) puts("% query failed (a packet predicate must succeed)"); else print_packet(qv[' + q.vars.length + '], nm, ' + q.vars.length + ');\n';
      main += '    printf("%% steps %ld, decisions %ld, %.4f ms per run\\n", (dl_steps - s0) / reps, (dl_decisions - d0) / reps, (t1 - t0) / reps);\n  }\n';
    });
    main += '  return 0;\n}\n';
    const atomInit = [...atoms.keys()].map((n, i) => '  AT[' + i + '] = mk_atom(' + cstrBytes(n) + ');').join('\n');
    const fnInit = [...fns.keys()].map((n, i) => '  FN[' + i + '] = intern(' + cstrBytes(n) + ');').join('\n');
    const header = '/* C generated by pl2detlog from Detlog (' + (opts.mode || 'Detlog') + ').\n   Build: cc -O2 -o prog prog.c -lm    Run: ./prog    Time: ./prog -r 1000\n' +
      (warnings.length ? '   Warnings:\n' + warnings.map(w => '   - ' + w).join('\n') + '\n' : '') + '*/\n';
    const lib = P.C_RUNTIME || '#include "runtime.c"\n';
    const tables = 'static Term *AT[' + Math.max(1, atoms.size) + '];\nstatic const char *FN[' + Math.max(1, fns.size) + '];\n' +
      'static Term *mk_list(int n, Term **xs, Term *tail) { Term *r = tail; for (int i = n; i-- > 0;) r = mk_cons(xs[i], r); return r; }\n' +
      'static void init_tables(void) {\n' + atomInit + '\n' + fnInit + '\n}\n';
    const code = header + lib + '\n/* ---------- program ---------- */\n' + tables + protos.join('\n') + '\n\n' + defs.join('\n') + '\n' + main;
    return { code, warnings };
  }
  P.toC = toC;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
