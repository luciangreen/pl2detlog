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

  // run-time support for native functions: bail-out by longjmp to the entry, integer helpers that bail where
  // the generic code would raise an error, ground equality, and tables for memoised calls on an integer
  const NATIVE_C = `
/* ---------- native tier ---------- */
#include <setjmp.h>
/* an input the native function may take: any bound term when unchecked (the contract says it is ground) */
#ifdef DL_CHECKED
#define DL_GROUND(t) is_ground(t)
#else
#define DL_GROUND(t) 1
#endif
/* GCC and Clang have a light setjmp (frame, stack and resume address only); otherwise the standard one */
#if defined(__GNUC__)
typedef void *nat_jmp[5];
#define NAT_SETJMP(b) __builtin_setjmp(b)
#define NAT_LONGJMP(b) __builtin_longjmp(b, 1)
#else
typedef jmp_buf nat_jmp;
#define NAT_SETJMP(b) setjmp(b)
#define NAT_LONGJMP(b) longjmp(b, 1)
#endif
static nat_jmp *nat_jb; static long nat_epoch = 0;
static void nat_bail(void) __attribute__((noinline));
static void nat_bail(void) { NAT_LONGJMP(*nat_jb); }
#ifdef DL_CHECKED
static long long n_iv(Term *x) { x = deref(x); if (x->tag != T_INT) nat_bail(); return x->iv; }
#else
/* unchecked (the default): the type contract is assumed, so no tag test */
static inline long long n_iv(Term *x) { return deref(x)->iv; }
#endif
static int n_isv(Term *x, long long v) { x = deref(x); return x->tag == T_INT && x->iv == v; }
static int n_eq(Term *a, Term *b) {
  a = deref(a); b = deref(b); if (a == b) return 1; if (a->tag != b->tag) return 0;
  switch (a->tag) {
    case T_INT: return a->iv == b->iv; case T_FLT: return a->fv == b->fv; case T_STR: return !strcmp(a->name, b->name);
    case T_ATOM: return a->name == b->name;
    case T_CMP: if (a->name != b->name || a->arity != b->arity) return 0; for (int i = 0; i < a->arity; i++) if (!n_eq(a->args[i], b->args[i])) return 0; return 1;
  }
  return 0;
}
#ifdef DL_CHECKED
static long long n_idiv(long long a, long long b) { if (b == 0) nat_bail(); return a / b; }
#else
static inline long long n_idiv(long long a, long long b) { return a / b; } /* unchecked: no zero test */
#endif
#ifdef DL_CHECKED
static long long n_iadd(long long a, long long b) { long long r; if (__builtin_add_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_iadd(a, b) ((a) + (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_isub(long long a, long long b) { long long r; if (__builtin_sub_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_isub(a, b) ((a) - (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_imul(long long a, long long b) { long long r; if (__builtin_mul_overflow(a, b, &r)) nat_bail(); return r; }
#else
#define n_imul(a, b) ((a) * (b)) /* unchecked: no overflow test */
#endif
#ifdef DL_CHECKED
static long long n_imod(long long a, long long b) { if (b == 0) nat_bail(); long long m = a % b; if (m != 0 && ((m < 0) != (b < 0))) m += b; return m; }
#else
static inline long long n_imod(long long a, long long b) { long long m = a % b; if (m != 0 && ((m < 0) != (b < 0))) m += b; return m; }
#endif
#ifdef DL_CHECKED
static long long n_irem(long long a, long long b) { if (b == 0) nat_bail(); return a % b; }
#else
static inline long long n_irem(long long a, long long b) { return a % b; } /* unchecked: no zero test */
#endif
static long long n_min(long long a, long long b) { return a <= b ? a : b; }
static long long n_max(long long a, long long b) { return a >= b ? a : b; }
typedef struct { long long key; long ep; int st; long long iv; Term *tv; } NMS;
typedef struct { NMS *s; size_t cap, n; long ep; } NMT;
static size_t nmt_h(long long k, size_t cap) { return (size_t)(((unsigned long long)k * 0x9E3779B97F4A7C15ULL) >> 17) & (cap - 1); }
static NMS *nmt_get(NMT *t, long long k) {
  if (!t->s || t->ep != nat_epoch) return NULL;
  for (size_t i = nmt_h(k, t->cap);; i = (i + 1) & (t->cap - 1)) { NMS *s = &t->s[i]; if (s->ep != nat_epoch) return NULL; if (s->key == k) return s; }
}
static void nmt_put(NMT *t, long long k, int st, long long iv, Term *tv) {
  if (t->ep != nat_epoch) { t->ep = nat_epoch; t->n = 0; if (t->s) memset(t->s, 0, sizeof(NMS) * t->cap); }
  if (!t->s || (t->n + 1) * 2 > t->cap) {
    size_t oc = t->cap; NMS *os = t->s; t->cap = oc ? oc * 2 : 64; t->s = (NMS *)calloc(t->cap, sizeof(NMS)); t->n = 0;
    for (size_t i = 0; i < oc; i++) if (os[i].ep == nat_epoch) nmt_put(t, os[i].key, os[i].st, os[i].iv, os[i].tv);
    free(os);
  }
  size_t i = nmt_h(k, t->cap); while (t->s[i].ep == nat_epoch && t->s[i].key != k) i = (i + 1) & (t->cap - 1);
  if (t->s[i].ep != nat_epoch) t->n++;
  t->s[i].key = k; t->s[i].ep = nat_epoch; t->s[i].st = st; t->s[i].iv = iv; t->s[i].tv = tv;
}
`;
  // The hand-written C of the benchmark algorithms (as bench/reference.c), for queries that run one of them:
  // the program times it too and prints this program's speed as a % of C's.  Lists are cells from a bump
  // heap, reset before each run, as in bench/reference.c.
  const REF_C = `
/* ---------- hand-written C reference (bench/reference.c) ---------- */
typedef struct ref_cell { long head; struct ref_cell *tail; } ref_cell;
static ref_cell *ref_heap; static size_t ref_hp, ref_hcap;
static volatile long ref_sink;
static void ref_need(size_t n) { if (n > ref_hcap) { free(ref_heap); ref_hcap = n; ref_heap = (ref_cell *)malloc(n * sizeof(ref_cell)); if (!ref_heap) dl_die("out of memory", NULL); } }
static ref_cell *ref_cons(long h, ref_cell *t) { ref_cell *c = &ref_heap[ref_hp++]; c->head = h; c->tail = t; return c; }
static long ref_fib(long n) { if (n == 0) return 0; if (n == 1) return 1; return ref_fib(n - 1) + ref_fib(n - 2); }
static ref_cell *ref_app(ref_cell *a, ref_cell *l) { if (!a) return l; return ref_cons(a->head, ref_app(a->tail, l)); }
static ref_cell *ref_nrev(ref_cell *l) { if (!l) return NULL; return ref_app(ref_nrev(l->tail), ref_cons(l->head, NULL)); }
static ref_cell *ref_numlist(long lo, long hi) { ref_cell *r = NULL; for (long i = hi; i >= lo; i--) r = ref_cons(i, r); return r; }
static ref_cell *ref_doubles(ref_cell *l) { if (!l) return NULL; return ref_cons(2 * l->head, ref_doubles(l->tail)); }
static long ref_total(ref_cell *l) { long s = 0; for (; l; l = l->tail) s += l->head; return s; }
static int ref_no_attack(long q, const long *qs, int n, long d) { for (int i = 0; i < n; i++, d++) if (q == qs[i] + d || q == qs[i] - d) return 0; return 1; }
static int ref_safe(const long *qs, int n) { for (int i = 0; i < n; i++) if (!ref_no_attack(qs[i], qs + i + 1, n - i - 1, 1)) return 0; return 1; }
static long ref_sols; static long ref_solbuf[64][16];
static void ref_perm(long *rest, int nrest, long *out, int k, int n) {
  if (nrest == 0) { if (ref_safe(out, n)) { for (int i = 0; i < n; i++) ref_solbuf[ref_sols & 63][i] = out[i]; ref_sols++; } return; }
  for (int i = 0; i < nrest; i++) { long x = rest[i], tmp[16]; int m = 0; for (int j = 0; j < nrest; j++) if (j != i) tmp[m++] = rest[j]; out[k] = x; ref_perm(tmp, m, out, k + 1, n); }
}
static long ref_queens(int n) { long ns[16], out[16]; for (int i = 0; i < n; i++) ns[i] = i + 1; ref_sols = 0; ref_perm(ns, n, out, 0, n); return ref_sols; }
static long ref_pin(void) { long n = 0, acc = 0; for (long a = 0; a <= 9; a++) for (long b = 0; b <= 9; b++) for (long c = 0; c <= 9; c++) if (a + b + c == 25) { n++; acc += a * 100 + b * 10 + c; } ref_sink = acc; return n; }
static const int ref_par[][2] = { {0, 1}, {1, 2}, {2, 3} };
static int ref_ancs[16], ref_nanc;
static int ref_anc_bb(int z, int y) { int n = 0; for (int i = 0; i < 3; i++) if (ref_par[i][0] == z && ref_par[i][1] == y) n++; for (int i = 0; i < 3; i++) if (ref_par[i][0] == z) n += ref_anc_bb(ref_par[i][1], y); return n; }
static void ref_anc(int y) { for (int i = 0; i < 3; i++) if (ref_par[i][1] == y) ref_ancs[ref_nanc++] = ref_par[i][0]; for (int i = 0; i < 3; i++) for (int k = ref_anc_bb(ref_par[i][1], y); k > 0; k--) ref_ancs[ref_nanc++] = ref_par[i][0]; }
/* ms per run of a batch loop: batches grow until one takes 20 ms; then the median of 3 batches */
static double ref_ms(void (*run)(long)) {
  long n = 1; double t;
  for (;;) { double t0 = now_ms(); run(n); t = now_ms() - t0; if (t >= 20 || n >= (1L << 30)) break; n = t < 1 ? n * 16 : (long)(n * 24 / t) + 1; }
  double ts[3]; for (int b = 0; b < 3; b++) { double t0 = now_ms(); run(n); ts[b] = (now_ms() - t0) / n; }
  if (ts[0] > ts[1]) { double x = ts[0]; ts[0] = ts[1]; ts[1] = x; } if (ts[1] > ts[2]) { double x = ts[1]; ts[1] = ts[2]; ts[2] = x; } if (ts[0] > ts[1]) { double x = ts[0]; ts[0] = ts[1]; ts[1] = x; }
  return ts[1];
}
`;
  // one run of the hand-written algorithm, and the heap cells it needs
  const refBody = r => ({
    fib: ['ref_sink = ref_fib(' + r.n + ');', 0],
    nrev: ['ref_sink = ref_nrev(ref_numlist(1, ' + r.n + '))->head;', r.n * 2 + r.n * (r.n + 1) / 2 + 16],
    doubles: ['ref_sink = ref_total(ref_doubles(ref_numlist(1, ' + r.n + ')));', r.n * 2 + 16],
    queens: ['ref_sink = ref_queens(' + r.n + ');', 0],
    pin: ['ref_sink = ref_pin();', 0],
    anc: ['ref_nanc = 0; ref_anc(3); ref_sink = ref_nanc;', 0],
  })[r.alg];
  function toC(detlogText, opts) {
    opts = opts || {};
    const prog = P.loadProgram(detlogText);
    // the original Prolog (opts.source), for the algebra that reads predicates as they were written
    let srcProg = null; try { srcProg = opts.source ? P.loadProgram(opts.source) : null; } catch (e) { srcProg = null; }
    const proofNotes = [];
    const warnings = []; const warned = new Set();
    const warn = m => { if (!warned.has(m)) { warned.add(m); warnings.push(m); } };
    const atoms = new Map(), fns = new Map();
    const atomIx = n => { if (!atoms.has(n)) atoms.set(n, atoms.size); return 'AT[' + atoms.get(n) + ']'; };
    const fnIx = n => { if (!fns.has(n)) fns.set(n, fns.size); return 'FN[' + fns.get(n) + ']'; };
    const pfn = k => 'p_' + mangle(k.replace('/', '_'));
    let uid = 0;
    const defs = [], protos = [];

    // a ground compound term is built once, at startup (KC table), and shared: unification never
    // writes into a term without variables, so every call may use the same cells
    const groundT = t => { t = D(t); if (t.t === 'v') return false; if (t.t === 'c') { for (const a of t.a) if (!groundT(a)) return false; } return true; };
    function termC(t, vm, top = true) {
      t = D(t);
      if (top && t.t === 'c' && !opts.noHoist && groundT(t)) return KC(t);
      switch (t.t) {
        case 'v': { if (!t.name || t.name === '_') return 'mk_var()'; const v = vm.get(t); if (!v) throw new Error('unknown variable ' + t.name); return v; }
        case 'n': return t.f ? 'mk_flt(' + (Number.isFinite(t.v) ? String(t.v) + (/[.e]/i.test(String(t.v)) ? '' : '.0') : (t.v > 0 ? 'INFINITY' : t.v < 0 ? '-INFINITY' : 'NAN')) + ')' : 'mk_int(' + t.v + 'LL)';
        case 'a': return atomIx(t.n);
        case 's': return 'mk_str(' + cstrBytes(t.v) + ')';
        case 'c': {
          if (t.f === '.' && t.a.length === 2) {
            const items = []; let x = t;
            while (x.t === 'c' && x.f === '.' && x.a.length === 2) { items.push(termC(x.a[0], vm, top)); x = D(x.a[1]); }
            return 'mk_list(' + items.length + ', (Term*[]){' + items.join(', ') + '}, ' + termC(x, vm) + ')';
          }
          return 'mk_cmp(' + fnIx(t.f) + ', ' + t.a.length + ', (Term*[]){' + t.a.map(x => termC(x, vm, top)).join(', ') + '})';
        }
      }
      throw new Error('bad term');
    }
    function argsC(as, vm) { return as.length ? '(Term*[]){' + as.map(x => termC(x, vm)).join(', ') + '}' : 'NULL'; }
    // generate-and-test fusion, as in the JIT (detlog_fast.js fuseGenLoop):
    //   builtin_rows(G, P), splice_extend(P, [G], e(Env), R2), loop(R2, R1)
    // with G member/2 or permutation/2 over a proper list and loop a packet loop (no cut) whose row predicate
    // starts by copying its row.  Each solution is bound in place; a DET filter row predicate runs through the
    // native entry and only kept rows are copied; otherwise the row predicate runs and its rows are copied.
    const isCT = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; };
    function fusionPlan(g1, g2, g3, rest) {
      if (P.key(g1) !== 'builtin_rows/2' || P.key(g2) !== 'splice_extend/4' || !P.loopShape) return null;
      const G = D(g1.a[0]), Pv = D(g1.a[1]), gk = P.key(G);
      if ((gk !== 'member/2' && gk !== 'permutation/2') || Pv.t !== 'v' || D(g2.a[0]) !== Pv) return null;
      const pat = P.listToArray(g2.a[1]); if (!pat || pat.length !== 1 || P.show(pat[0]) !== P.show(G)) return null;
      const R2 = D(g2.a[3]); if (R2.t !== 'v' || !g3.a || g3.a.length !== 2 || D(g3.a[0]) !== R2) return null;
      const k3 = P.key(g3); const lcls = prog.preds.get(k3); if (!lcls) return null;
      const sh = P.loopShape(k3, lcls); if (!sh || sh.cutVariant || !prog.preds.has(sh.callKey)) return null;
      const rcl = prog.preds.get(sh.callKey).find(c => isCT(D(c.head).a[0], 'e', 1));
      if (!rcl) return null;
      const rb = P.flatConj(rcl.body).map(D);
      if (P.key(rb[0]) !== 'copy_term/2' || D(rb[0].a[0]) !== D(D(D(rcl.head).a[0]).a[0])) return null;
      if (rest.concat([g3.a[1]]).some(x => P.termVars(x).some(v => v === Pv || v === R2)) || P.termVars(g2.a[2]).includes(R2)) return null;
      const env = g2.a[2]; if (!isCT(env, 'e', 1)) return null;
      let filt = null;
      const Lr = P.listToArray(rb[0].a[1]), Ev = P.listToArray(D(env).a[0]), ic = rb[1];
      if (rb.length === 2 && Lr && Ev && Lr.length === Ev.length && Lr.every(v => D(v).t === 'v') && P.key(ic) === 'if_commit/3') {
        const c = P.flatConj(ic.a[0]).map(D), th = D(ic.a[1]);
        if (c.length === 2 && c[0].t === 'c' && /__d$/.test(c[0].f) && P.key(c[1]) === '\\==/2' && D(c[1].a[0]) === D(c[0].a[c[0].a.length - 1]) && P.key(th) === 'if_commit/3') {
          const Sv = D(c[0].a[c[0].a.length - 1]), yes = D(th.a[0]), keep = D(th.a[1]), drop = D(th.a[2]), Orow = D(D(rcl.head).a[1]);
          const okYes = P.key(yes) === '=/2' && D(yes.a[0]) === Sv && D(yes.a[1]).t === 'a' && D(yes.a[1]).n === 'yes';
          const okKeep = P.key(keep) === '=/2' && D(keep.a[0]) === Orow && P.show(keep.a[1]) === P.show(P.list([P.Cmp('e', [P.list(Lr)])]));
          const okDrop = P.key(drop) === '=/2' && D(drop.a[0]) === Orow && D(drop.a[1]).t === 'a' && D(drop.a[1]).n === '[]';
          const sub = new Map(Lr.map((v, i) => [D(v), Ev[i]]));
          const subst = t => { t = D(t); if (t.t === 'v') return sub.has(t) ? sub.get(t) : null; if (t.t === 'c') { const a = t.a.map(subst); return a.includes(null) ? null : P.Cmp(t.f, a); } return t; };
          const args = c[0].a.slice(0, -1).map(subst);
          if (okYes && okKeep && okDrop && !args.includes(null) && natModes.has(P.key(c[0]))) filt = { k: P.key(c[0]), args };
        }
      }
      return { gk, G, env, out: g3.a[1], rowKey: sh.callKey, filt };
    }
    function fusedC(pl, generic, vm, fail, ind) {
      const n = ++uid, list = pl.gk === 'member/2' ? pl.G.a[1] : pl.G.a[0], x = pl.gk === 'member/2' ? pl.G.a[0] : pl.G.a[1];
      const body = y => 'size_t m = TR_TOP; if (unify(x' + n + ', ' + y + ')) { STEP(); STEP(); STEP(); STEP(); if (++nrow' + n + ' > 1000000) dl_die("builtin_rows: infinite generator", NULL);\n' +
        (pl.filt ? '  Term *Sv = mk_var(); Term **fa = (Term*[]){' + pl.filt.args.map(a => termC(a, vm)).concat(['Sv']).join(', ') + '};\n  if (' + natEntryFn(pl.filt.k) + '(fa)) { if (deref(Sv) == ' + atomIx('yes') + ') tv_push(&res' + n + ', copy_term(ev' + n + ')); }\n  else ' : '  ') +
        '{ Term *Ov = mk_var(); if (!' + pfn(pl.rowKey) + '((Term*[]){ ev' + n + ', Ov })) ok' + n + ' = 0; else { TV o1 = { 0 }; list_to_tv(Ov, &o1); for (size_t j = 0; j < o1.n; j++) tv_push(&res' + n + ', copy_term(o1.v[j])); tv_free(o1.v); } }\n' +
        '} undo(m);';
      let loop;
      // permutation(Xs, Ys) tested by a native DET predicate on Ys alone, with no outputs: each permutation
      // is written into the same k list cells (the test is pure and keeps nothing), the native function is
      // called directly in its 'i' mode, and only a kept permutation is built as a new list and copied.
      // permutation(Xs, Ys) tested by a pairwise test (src/algebra.js): each element is tested against those
      // already placed and a failing prefix is dropped; the lists kept are the same, in the same order.
      const pw = pl.filt && pl.gk === 'permutation/2' && srcProg && pl.filt.args.length === 1 && D(pl.filt.args[0]) === D(x) && /__d\/\d+$/.test(pl.filt.k) ? P.pairwise(srcProg, pl.filt.k.replace(/__d\/(\d+)$/, (_, a) => '/' + (+a - 1))) : null;
      if (pw) {
        proofNotes.push(pw.proof);
        const keep = 'Term *y = tv_list(&cur); size_t m = TR_TOP; if (unify(x' + n + ', y)) tv_push(&res' + n + ', copy_term(ev' + n + ')); undo(m);';
        const test = pw.code('p', 'yv', 'dist', false);
        loop = '{ size_t k = xs' + n + '.n; int allint = 1; for (size_t i = 0; i < k; i++) if (deref(xs' + n + '.v[i])->tag != T_INT) allint = 0;\n' +
          '  if (!allint) dl_die("pairwise generate-and-test needs a list of integers", NULL);\n' +
          '  long long *val = (long long *)malloc(sizeof(long long) * (k + 1)), *pl = (long long *)malloc(sizeof(long long) * (k + 1)); for (size_t i = 0; i < k; i++) val[i] = deref(xs' + n + '.v[i])->iv;\n' +
          '  size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
          '  for (; ok' + n + ';) {\n' +
          '    if ((size_t)d == k) { ' + keep + '\n      d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
          '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    { long long yv = val[idx[d]]; int okp = 1; for (long i = d - 1; i >= 0; i--) { long long p = pl[i], dist = ' + pw.c0 + ' + (d - 1 - i); if (!(' + test + ')) { okp = 0; break; } } if (!okp) { idx[d]++; continue; } }\n' +
          '    used[idx[d]] = 1; pl[d] = val[idx[d]]; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); free(val); free(pl); }\n';
      } else {
      const md = pl.filt && pl.gk === 'permutation/2' && pl.filt.args.length === 1 && D(pl.filt.args[0]) === D(x) && (natModes.get(pl.filt.k) || []).find(m => m.mode === 'i');
      if (md) {
        const keep = 'Term *y = tv_list(&cur); size_t m = TR_TOP; if (unify(x' + n + ', y)) tv_push(&res' + n + ', copy_term(ev' + n + ')); undo(m);';
        loop = '{ size_t k = xs' + n + '.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
          '  Term **cell = (Term **)malloc(sizeof(Term *) * (k + 1)); for (size_t i = 0; i < k; i++) cell[i] = mk_cons(NIL, NIL), cell[i]->cpe = 0; /* the cells are reused: not ground-marked */ for (size_t i = 0; i + 1 < k; i++) cell[i]->args[1] = cell[i + 1]; cell[k] = NIL;\n' +
          '  for (; ok' + n + ';) {\n' +
          '    if ((size_t)d == k) {\n' +
          '      for (size_t i = 0; i < k; i++) cell[i]->args[0] = cur.v[i];\n' +
          '      if (++nrow' + n + ' > 1000000) dl_die("builtin_rows: infinite generator", NULL);\n' +
          '      int r; { nat_jmp jb; nat_jmp *sv = nat_jb; nat_jb = &jb; nat_epoch++; if (NAT_SETJMP(jb)) { nat_jb = sv; r = 2; } else { r = ' + md.name + '(cell[0]); nat_jb = sv; } }\n' +
          '      if (r == 1) { ' + keep + ' }\n' +
          '      else if (r == 2) { Term *y = tv_list(&cur); { ' + body('y') + ' } }\n' +
          '      d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
          '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
          '    used[idx[d]] = 1; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); free(cell); }\n';
      } else if (pl.gk === 'member/2') loop = 'for (size_t i = 0; i < xs' + n + '.n && ok' + n + '; i++) { ' + body('xs' + n + '.v[i]') + ' }\n';
      else loop = '{ size_t k = xs' + n + '.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
        '  for (; ok' + n + ';) {\n' +
        '    if ((size_t)d == k) { Term *y = tv_list(&cur); { ' + body('y') + ' } d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
        '    while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
        '    if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
        '    used[idx[d]] = 1; tv_push(&cur, xs' + n + '.v[idx[d]]); d++; idx[d] = 0;\n  }\n  free(idx); free(used); tv_free(cur.v); }\n';
      }
      return ind + '{ TV xs' + n + ' = { 0 };\n' + ind + 'if (!list_to_tv(' + termC(list, vm) + ', &xs' + n + ')) {\n' + ind + 'tv_free(xs' + n + '.v);\n' + generic + ind + '} else {\n' +
        ind + 'Term *x' + n + ' = ' + termC(x, vm) + ', *ev' + n + ' = ' + termC(pl.env, vm) + '; TV res' + n + ' = { 0 }; size_t nrow' + n + ' = 0; int ok' + n + ' = 1; STEP(); STEP(); STEP();\n' +
        loop + ind + 'tv_free(xs' + n + '.v);\n' + ind + 'if (!ok' + n + ') { tv_free(res' + n + '.v); ' + fail + ' }\n' +
        ind + '{ Term *rl = tv_list(&res' + n + '); tv_free(res' + n + '.v); if (!unify(' + termC(pl.out, vm) + ', rl)) ' + fail + ' } } }\n';
    }
    function stmt(g, vm, fail, ind) {
      g = D(g); const k = P.key(g); const as = g.t === 'c' ? g.a : [];
      if (g.t === 'v') throw new Error('variable goal');
      if (k === ',/2') {
        const gs = P.flatConj(g).map(D); let code = '';
        for (let i = 0; i < gs.length; i++) {
          const pl = i + 2 < gs.length && fusionPlan(gs[i], gs[i + 1], gs[i + 2], gs.slice(i + 3));
          if (pl) { code += fusedC(pl, stmt(gs[i], vm, fail, ind) + stmt(gs[i + 1], vm, fail, ind) + stmt(gs[i + 2], vm, fail, ind), vm, fail, ind); i += 2; continue; }
          code += stmt(gs[i], vm, fail, ind);
        }
        return code;
      }
      switch (k) {
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
      if (prog.preds.has(k)) {
        // stream code's pruned permutation T__pwperm(L, [], P, K) (src/stream.js), as in the JIT: a native
        // integer loop over the pairwise test; each kept permutation runs the continuation K, and an answer
        // that commits stops the loop.  A list that is not all integers runs the clauses.
        if (k.endsWith('__pwperm/4') && srcProg && prog.preds.has('dl_k/1')) {
          let pw = null; try { pw = P.pairwise(srcProg, g.f.slice(0, -'__pwperm'.length) + '/1'); } catch (e) { pw = null; }
          if (pw) {
            proofNotes.push(pw.proof);
            const n = ++uid, test = pw.code('p', 'yv', 'dist', false), a = as.map(x => termC(x, vm));
            return ind + '{ Term *L' + n + ' = ' + a[0] + ', *Pre' + n + ' = ' + a[1] + ', *P' + n + ' = ' + a[2] + ', *K' + n + ' = ' + a[3] + '; TV xs = { 0 }; int found = 0, native = list_to_tv(L' + n + ', &xs) && deref(Pre' + n + ') == NIL && deref(P' + n + ')->tag == T_VAR;\n' +
              ind + '  for (size_t i = 0; native && i < xs.n; i++) if (deref(xs.v[i])->tag != T_INT) native = 0;\n' +
              ind + '  if (!native) found = ' + pfn(k) + '((Term*[]){ L' + n + ', Pre' + n + ', P' + n + ', K' + n + ' });\n' +
              ind + '  else { size_t k = xs.n; long long *val = (long long *)malloc(sizeof(long long) * (k + 1)), *pl = (long long *)malloc(sizeof(long long) * (k + 1)); for (size_t i = 0; i < k; i++) val[i] = deref(xs.v[i])->iv;\n' +
              ind + '    size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; TV cur = { 0 };\n' +
              ind + '    for (;;) { STEP();\n' +
              ind + '      if ((size_t)d == k) { Term *y = tv_list(&cur); size_t m = TR_TOP; if (unify(P' + n + ', y) && ' + pfn('dl_k/1') + '((Term*[]){ K' + n + ' })) { found = 1; break; } undo(m);\n' +
              ind + '        d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
              ind + '      while (idx[d] < k && used[idx[d]]) idx[d]++;\n' +
              ind + '      if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }\n' +
              ind + '      { long long yv = val[idx[d]]; int okp = 1; for (long i = d - 1; i >= 0; i--) { long long p = pl[i], dist = ' + pw.c0 + ' + (d - 1 - i); if (!(' + test + ')) { okp = 0; break; } } if (!okp) { idx[d]++; continue; } }\n' +
              ind + '      used[idx[d]] = 1; pl[d] = val[idx[d]]; tv_push(&cur, xs.v[idx[d]]); d++; idx[d] = 0;\n' +
              ind + '    }\n' + ind + '    free(idx); free(used); tv_free(cur.v); free(val); free(pl); }\n' +
              ind + '  tv_free(xs.v); if (!found) ' + fail + ' }\n';
          }
        }
        if (natModes.has(k) && /__d$/.test(g.f) && !/__d$/.test(curPred)) return ind + '{ Term **na = ' + (as.length ? argsC(as, vm) : 'NULL') + '; if (!' + natEntryFn(k) + '(na) && !' + pfn(k) + '(na)) ' + fail + ' }\n';
        return ind + 'if (!' + pfn(k) + '(' + argsC(as, vm) + ')) ' + fail + '\n';
      }
      if (!C_BUILTINS.has(k)) warn('builtin ' + k + ' is not in the C runtime');
      // the common type tests and unifications are written in place (no dispatch by name); checked builds keep
      // bi_call, which counts steps
      if (!opts.checked) {
        const A = () => termC(as[0], vm), B = () => termC(as[1], vm);
        switch (k) {
          case '=/2': return ind + 'if (!unify(' + A() + ', ' + B() + ')) ' + fail + '\n';
          case 'var/1': return ind + 'if (deref(' + A() + ')->tag != T_VAR) ' + fail + '\n';
          case 'nonvar/1': return ind + 'if (deref(' + A() + ')->tag == T_VAR) ' + fail + '\n';
          case '==/2': return ind + 'if (compare(' + A() + ', ' + B() + ') != 0) ' + fail + '\n';
          case '\\==/2': return ind + 'if (compare(' + A() + ', ' + B() + ') == 0) ' + fail + '\n';
          case 'copy_term/2': return ind + 'if (!unify(' + B() + ', copy_term(' + A() + '))) ' + fail + '\n';
        }
      }
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
    // ---------- native tier (src/native.js) for the modes the program's queries use ----------
    // The JS engine runs the queries once (a profile); every (predicate, mode) its native tier compiled is
    // compiled here too, to C: long long for integers, outputs through pointers, longjmp to bail out.
    let nativeModes = opts.nativeModes;
    if (!nativeModes && opts.native !== false && P.runDetlogFast && P.nativeModesOf && P.DETLOG_NATIVE !== false) {
      const np = P.loadProgram(detlogText);
      for (const q of opts.queries || []) { try { P.runDetlogFast(np, q.pred, q.vars, { stepLimit: opts.profileSteps || 2e7 }); } catch (e) { /* the profile only gathers modes */ } }
      nativeModes = P.nativeModesOf(np);
    }
    const kcs = [], kcIx = new Map();
    const KC = t => { const key = P.show(t, { quoted: true }) + '|' + (t.t === 'n' ? (t.f ? 'f' : 'i') : t.t); if (!kcIx.has(key)) { kcIx.set(key, kcs.length); kcs.push(t); } return 'KC[' + kcIx.get(key) + ']'; };
    const nTables = new Map();
    const sigs = new Map();
    const cname = (name, int) => name + (int ? '_i' : '_t');
    const EMC = {
      YES: '1', NO: '0', MAYBE: '2', EQOP: '==', NEOP: '!=', BAIL: 'nat_bail();',
      v: (name, int) => cname(name, int),
      num: v => v + 'LL',
      k: t => t.t === 'a' ? atomIx(t.n) : KC(t),
      box: e => 'mk_int(' + e + ')',
      unbox: e => 'n_iv(' + e + ')',
      cmp: (f, args) => f === '.' && args.length === 2 ? (opts.checked ? 'mk_cons(' : 'mk_gcons(') + args[0] + ', ' + args[1] + ')' : 'mk_cmp(' + fnIx(f) + ', ' + args.length + ', (Term*[]){' + args.join(', ') + '})',
      eq: (a, b) => 'n_eq(' + a + ', ' + b + ')',
      isIntVal: (e, v) => 'n_isv(' + e + ', ' + v + ')',
      tmp: (t, e) => 'Term *' + t + ' = deref(' + e + ');',
      isCmp: (t, f, n) => t + '->tag == T_CMP && ' + t + '->name == ' + (f === '.' ? 'A_DOT->name' : fnIx(f)) + ' && ' + t + '->arity == ' + n,
      arg: (t, i) => t + '->args[' + i + ']',
      keyTest: (pat, t) => {
        if (pat.t === 'a') return t + ' == ' + atomIx(pat.n);
        if (pat.t === 'n') return pat.f ? t + '->tag == T_FLT && ' + t + '->fv == ' + (Number.isFinite(pat.v) ? String(pat.v) + (/[.e]/i.test(String(pat.v)) ? '' : '.0') : (pat.v > 0 ? 'INFINITY' : pat.v < 0 ? '-INFINITY' : 'NAN')) : t + '->tag == T_INT && ' + t + '->iv == ' + pat.v + 'LL';
        if (pat.t === 's') return t + '->tag == T_STR && !strcmp(' + t + '->name, ' + cstrBytes(pat.v) + ')';
        return '0';
      },
      fn: (name, args) => ({ IDIV: 'n_idiv', IMOD: 'n_imod', IREM: 'n_irem', MIN: 'n_min', MAX: 'n_max', ABS: 'llabs', IADD: 'n_iadd', ISUB: 'n_isub', IMUL: 'n_imul' })[name] + '(' + args.join(', ') + ')',
      assign: (lhs, rhs) => lhs + ' = ' + rhs + ';\n',
      fail: L => 'goto ' + L + ';',
      blockNoThen: (L, rc, re) => '{\n' + rc + '}\n' + L + ': ;\n' + re,
      block: (L, ok, rc, rt, re) => '{ int ' + ok + ' = 0;\n{\n' + rc + ok + ' = 1;\n}\n' + L + ': ;\nif (' + ok + ') {\n' + rt + '} else {\n' + re + '}\n}\n',
      retOuts: vals => vals.map((v, i) => '*o' + i + ' = ' + v + ';').join(' ') + ' return 1;',
      retStatus: v => 'return ' + v + ';',
      call: (callee, ins, outs, retInt, rs, memo) => {
        const args = ins.concat(outs.map(o => '&' + o)).join(', ');
        // memoised in a table keyed by the one integer input
        if (memo && /^n?o?$/.test(memo.mode) && memo.mode.startsWith('n') && ins.length === 1 && outs.length <= 1) {
          if (!nTables.has(memo.table)) nTables.set(memo.table, 'NT' + nTables.size);
          const T = nTables.get(memo.table), fld = retInt ? 'iv' : 'tv';
          const fill = outs.length ? 'if (' + rs + ' == 1) ' + outs[0] + ' = ms->' + fld + ';' : '';
          return '{ NMS *ms = nmt_get(&' + T + ', ' + ins[0] + '); if (ms) { ' + rs + ' = ms->st; ' + fill + ' } else { ' + rs + ' = ' + callee + '(' + args + '); nmt_put(&' + T + ', ' + ins[0] + ', ' + rs + ', ' + (outs.length && retInt ? '(' + rs + ' == 1 ? ' + outs[0] + ' : 0)' : '0') + ', ' + (outs.length && !retInt ? '(' + rs + ' == 1 ? ' + outs[0] + ' : NULL)' : 'NULL') + '); } }\n';
        }
        return rs + ' = ' + callee + '(' + args + ');\n';
      },
      func: (name, params, nOuts, selfInt, used, statusLocals, body) => {
        const ps = params.map(p => (p.int ? 'long long ' : 'Term *') + cname(p.name, p.int));
        for (let i = 0; i < nOuts; i++) ps.push((nOuts === 1 && selfInt ? 'long long *' : 'Term **') + 'o' + i);
        const sig = 'static int ' + name + '(' + (ps.length ? ps.join(', ') : 'void') + ')';
        sigs.set(name, sig);
        const decl = used.map(u => (u.int ? 'long long ' : 'Term *') + cname(u.name, u.int) + (u.int ? ' = 0;' : ' = NULL;')).join(' ') + (statusLocals.length ? ' int ' + statusLocals.map(x => x + ' = 0').join(', ') + ';' : '');
        return sig + ' {\n  STEP();\n  ' + decl + '\n' + body + '  nat_bail(); return 0;\n}\n';
      },
    };
    // Last calls in the native tier (unchecked), so that list recursions run as loops:
    //  1. s = f(A, &v); if (s != 1) return s; *o = v; return 1;      ==>  return f(A, o);
    //     (f's result code is passed on unchanged and *o is read only after success)
    //  2. s = f(A, &v); if (s != 1) return s; *o = cons(H, v); return 1;  ==>  c = cons(H, NULL); *o = c; return f(A, &c->args[1]);
    //     (destination passing: H does not mention v, so it may be built first; on failure the caller ignores *o)
    // f must be the function itself, so the call is a self tail call that the C compiler turns into a jump.
    function lastCalls(src) {
      const m = /^static int (nat\d+)\(/m.exec(src); if (!m) return src;
      const f = m[1];
      const esc = x => x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const splitArgs = t => { const out = []; let d = 0, cur = ''; for (const ch of t) { if (ch === '(') d++; if (ch === ')') d--; if (ch === ',' && d === 0) { out.push(cur.trim()); cur = ''; } else cur += ch; } if (cur.trim()) out.push(cur.trim()); return out; };
      const re = new RegExp('\\{ (s\\d+) = ' + esc(f) + '\\((.*)\\);\\nif \\(\\1 != 1\\) return \\1;\\n((?:\\*o\\d+ = [^;]*; )+)return 1; \\}', 'g');
      return src.replace(re, (all, sv, argText, asg) => {
        const args = splitArgs(argText);
        const outs = []; while (args.length && /^&v\d+_[a-z]$/.test(args[args.length - 1])) outs.unshift(args.pop().slice(1));
        if (!outs.length) return all;
        const assigns = [...asg.matchAll(/\*(o\d+) = ([^;]*); /g)].map(x => ({ o: x[1], e: x[2] }));
        if (assigns.length !== outs.length) return all;
        const mentions = (e, v) => new RegExp('\\b' + v + '\\b').test(e);
        const pre = [], slot = [];
        for (const v of outs) {
          const as = assigns.filter(x => mentions(x.e, v)); if (as.length !== 1) return all;
          const { o, e } = as[0];
          if (e === v) { slot.push(o); continue; }
          const c = /^mk_gcons\((.*), (v\d+_t)\)$/.exec(e);
          if (!c || c[2] !== v || outs.some(w => mentions(c[1], w))) return all;
          const cv = 'c' + pre.length + '_';
          pre.push('Term *' + cv + ' = mk_gcons(' + c[1] + ', NULL); *' + o + ' = ' + cv + ';');
          slot.push('&' + cv + '->args[1]');
        }
        return '{ ' + pre.join(' ') + (pre.length ? ' ' : '') + 'return ' + f + '(' + args.concat(slot).join(', ') + '); }';
      });
    }
    const nDone = new Map(); const nDefs = []; let nSeq = 0;
    const natModes = new Map(); // predicate key -> [{ mode, name, retInt }]
    for (const km of nativeModes || []) {
      const i = km.lastIndexOf('|'); const k = km.slice(0, i), mode = km.slice(i + 1);
      if (nDone.has(km) || !prog.preds.has(k)) continue;
      const batch = P.nativeBatch(prog, k, mode, EMC, { has: x => nDone.has(x), get: x => nDone.get(x) }, () => 'nat' + (nSeq++));
      if (!batch) { nDone.set(km, null); warn('native function for ' + km + ' not compiled to C'); continue; }
      for (const [key2, e] of batch) { nDone.set(key2, { ref: e.name, retInt: e.retInt }); nDefs.push(opts.checked ? e.src : lastCalls(e.src)); }
    }
    for (const km of nativeModes || []) {
      const f = nDone.get(km); if (!f) continue;
      const i = km.lastIndexOf('|'); const k = km.slice(0, i);
      if (!natModes.has(k)) natModes.set(k, []);
      natModes.get(k).push({ mode: km.slice(i + 1), name: f.ref, retInt: f.retInt });
    }
    // entry from packet code: the argument modes decide; a compiled mode runs natively, otherwise p__d runs
    const natEntryFn = k => 'nat_' + pfn(k);
    const natEntries = [];
    for (const [k, ms] of natModes) {
      const n = +k.slice(k.lastIndexOf('/') + 1) - 1;
      let c = 'static int ' + natEntryFn(k) + '(Term **a) {\n  Term *x[' + Math.max(1, n) + ']; char m[' + (n + 1) + '];\n';
      c += '  for (int i = 0; i < ' + n + '; i++) { x[i] = deref(a[i]); if (x[i]->tag == T_VAR) { for (int j = 0; j < i; j++) if (x[j] == x[i]) return 0; m[i] = \'o\'; } else if (x[i]->tag == T_INT) m[i] = \'n\'; else if (DL_GROUND(x[i])) m[i] = \'i\'; else return 0; }\n';
      c += '  m[' + n + '] = 0; Term *S = deref(a[' + n + ']); if (S->tag != T_VAR) return 0; for (int i = 0; i < ' + n + '; i++) if (x[i] == S) return 0;\n';
      for (const md of ms) {
        const outs = [...md.mode].map((ch, i) => ch === 'o' ? i : -1).filter(i => i >= 0);
        const ins = [...md.mode].map((ch, i) => ch === 'n' ? 'x[' + i + ']->iv' : ch === 'i' ? 'x[' + i + ']' : null).filter(Boolean);
        const intOut = outs.length === 1 && md.retInt;
        c += '  if (!strcmp(m, "' + md.mode + '")) {\n    ' + outs.map((o, j) => (intOut ? 'long long' : 'Term *') + ' o' + j + ' = 0;').join(' ') + '\n';
        c += '    nat_jmp jb; nat_jmp *sv = nat_jb; nat_jb = &jb; nat_epoch++;\n    if (NAT_SETJMP(jb)) { nat_jb = sv; return 0; }\n';
        c += '    int r = ' + md.name + '(' + ins.concat(outs.map((o, j) => '&o' + j)).join(', ') + ');\n    nat_jb = sv;\n';
        c += '    if (r == 2) return 0;\n    if (r == 0) { bind(S, ' + atomIx('no') + '); return 1; }\n';
        c += '    ' + outs.map((o, j) => 'bind(x[' + o + '], ' + (intOut ? 'mk_int(o' + j + ')' : 'o' + j) + ');').join(' ') + ' bind(S, ' + atomIx('yes') + '); return 1;\n  }\n';
      }
      c += '  return 0;\n}\n';
      natEntries.push(c);
    }
    let curPred = '';

    for (const k of prog.order) {
      curPred = k.slice(0, k.lastIndexOf('/'));
      const cls = prog.preds.get(k); const f = pfn(k);
      protos.push('static int ' + f + '(Term **a);');
      const parts = [];
      cls.forEach((cl, i) => {
        const vm = new Map(); let vi = 0;
        const vs = P.termVars(P.Cmp('-', [cl.head, cl.body])).filter(v => v.name && v.name !== '_');
        for (const v of vs) vm.set(v, 'v' + (++vi));
        const head = D(cl.head); const hargs = head.t === 'c' ? head.a : [];
        let body = 'static int ' + f + '_c' + (i + 1) + '(Term **a) {\n';
        // a head argument that is a variable not seen in an earlier argument is that argument itself:
        // no fresh variable to make and bind (unchecked and checked alike: unify would only bind it)
        const alias = new Map(), seen = new Set();
        hargs.forEach((h, j) => { const d = D(h); if (d.t === 'v' && d.name && d.name !== '_' && !seen.has(d) && !alias.has(d)) alias.set(d, j); for (const v of P.termVars(h)) seen.add(v); });
        if (vs.length) body += '  Term ' + vs.map(v => '*' + vm.get(v) + ' = ' + (alias.has(v) ? 'a[' + alias.get(v) + ']' : 'mk_var()')).join(', ') + ';\n';
        body += '  (void)a;\n';
        hargs.forEach((h, j) => { const d = D(h); if (d.t === 'v' && alias.get(d) === j) return; body += '  if (!unify(a[' + j + '], ' + termC(h, vm) + ')) return 0;\n'; });
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
    // queries that run a benchmark algorithm, checked by the hand-written version giving exactly their answers
    const refs = new Map(), refFns = [];
    if (opts.cReference !== false && P.cRefPattern && P.runDetlogFast) {
      let rp = null;
      qs.forEach((q, i) => {
        if (!P.cRefPattern(q.text)) return;
        try {
          rp = rp || P.loadProgram(detlogText);
          const r = P.runDetlogFast(rp, q.pred, q.vars, { stepLimit: 2e7 });
          const ref = !r.error && P.cRefMatch(q.text, r.events);
          if (!ref) return;
          const [body, cells] = refBody(ref);
          refs.set(i, { fn: 'ref_q' + i, alg: ref.alg, cells });
          refFns.push('static void ref_q' + i + '(long reps) { for (long i = 0; i < reps; i++) { ref_hp = 0; ' + body + ' } }');
        } catch (e) { /* no reference for this query */ }
      });
    }
    let main = 'int main(int argc, char **argv) {\n  int reps = 1; if (argc > 2 && !strcmp(argv[1], "-r")) reps = atoi(argv[2]); if (reps < 1) reps = 1;\n  int refs = !(argc > 1 && !strcmp(argv[argc - 1], "--no-ref")); (void)refs; /* --no-ref: skip timing the hand-written C */\n  for (int i = 1; i < argc; i++) { if (!strcmp(argv[i], "--events")) ev_mode = 1; if (!strcmp(argv[i], "--first")) first_only = 1; }\n  double st0 = now_ms(); rt_init(); init_tables(); long lim0 = dl_step_limit;\n  printf("%% startup %.4f ms\\n", now_ms() - st0);\n';
    qs.forEach(q => {
      const k = q.pred + '__cp/' + (q.vars.length + 1);
      main += '  {\n    const char *nm[] = {' + (q.vars.length ? q.vars.map(cstrBytes).join(', ') : '""') + '};\n';
      main += '    Term *qv[' + (q.vars.length + 1) + ']; int ok = 0; long s0 = dl_steps, d0 = dl_decisions; double t0 = now_ms();\n';
      // every repetition but the last runs on memory that is released afterwards (the last one is printed)
      main += '    ArenaMark am = arena_mark(); size_t tm = TR_TOP;\n';
      main += '    for (int rep = 0; rep < reps; rep++) { if (rep) { undo(tm); arena_release(am); } dl_step_limit = dl_steps + lim0; /* the step limit is per run */ for (int i = 0; i < ' + (q.vars.length + 1) + '; i++) qv[i] = mk_var(); memo_clear(); ok = ' + pfn(k) + '(qv); }\n';
      main += '    double t1 = now_ms();\n';
      main += '    if (!ev_mode) printf("?- %s.\\n", ' + cstrBytes(q.text) + ');\n';
      main += '    if (!ok) puts("% query failed (a packet predicate must succeed)"); else { if (ev_mode) putchar(0x1d); print_packet(qv[' + q.vars.length + '], nm, ' + q.vars.length + '); if (ev_mode) putchar(0x1d); }\n';
      main += '    printf("%% steps %ld, decisions %ld, %.4f ms per run\\n", (dl_steps - s0) / reps, (dl_decisions - d0) / reps, (t1 - t0) / reps);\n';
      const ref = refs.get(qs.indexOf(q));
      if (ref) {
        // the same algorithm written by hand in C, timed in this process: this program's speed as a % of C's
        main += '    if (ok && refs) { ref_need(' + Math.max(16, Math.ceil(ref.cells)) + '); double rc = ref_ms(' + ref.fn + '), me = (t1 - t0) / reps;\n';
        main += '      printf("%% hand-written C (' + ref.alg + '): %.6f ms per run; this program runs at %.3g%% of C\'s speed%s\\n", rc, 100 * rc / me, reps < 10 ? " (one timing run: use -r N for a steady figure)" : ""); }\n';
      }
      main += '  }\n';
    });
    main += '  return 0;\n}\n';
    const kcInit = kcs.map((t, i) => '  KC[' + i + '] = ' + termC(t, new Map(), false) + ';').join('\n');
    const atomInit = [...atoms.keys()].map((n, i) => '  AT[' + i + '] = mk_atom(' + cstrBytes(n) + ');').join('\n');
    const fnInit = [...fns.keys()].map((n, i) => '  FN[' + i + '] = intern(' + cstrBytes(n) + ');').join('\n');
    const header = '/* C generated by pl2detlog from Detlog (' + (opts.mode || 'Detlog') + ').\n   Build: cc -O2 -o prog prog.c -lm    Run: ./prog    Time: ./prog -r 1000\n' +
      (proofNotes.length ? '   Algebra (src/algebra.js):\n' + [...new Set(proofNotes)].map(w => '   - ' + w.replace(/\*\//g, '* /')).join('\n') + '\n' : '') +
      (warnings.length ? '   Warnings:\n' + warnings.map(w => '   - ' + w).join('\n') + '\n' : '') + '*/\n';
    const lib = P.C_RUNTIME || '#include "runtime.c"\n';
    const natLib = nDefs.length ? NATIVE_C + [...nTables.values()].map(t => 'static NMT ' + t + ';').join('\n') + '\n' : '';
    const tables = 'static Term *AT[' + Math.max(1, atoms.size) + '];\nstatic const char *FN[' + Math.max(1, fns.size) + '];\nstatic Term *KC[' + Math.max(1, kcs.length) + '];\n' +
      'static Term *mk_list(int n, Term **xs, Term *tail) { Term *r = tail; for (int i = n; i-- > 0;) r = mk_cons(xs[i], r); return r; }\n' +
      'static void init_tables(void) {\n' + atomInit + '\n' + fnInit + '\n' + kcInit + '\n}\n';
    const natProtos = [...sigs.values()].map(x => x + ';').join('\n') + (refs.size ? REF_C + refFns.join('\n') + '\n' : '');
    // unchecked by default: no step limit, type tests, overflow or zero-divisor tests in native code;
    // opts.checked keeps them (and the step limit) for programs whose calls may break the contract
    const mode = opts.checked ? '#define DL_CHECKED 1 /* checked: step limit, type, overflow and zero tests */\n' : '/* unchecked (the default): calls are assumed to meet the type contract; build with -DDL_CHECKED for the checks */\n';
    const swiMode = opts.swiWrite ? '#define DL_SWI_WRITE 1 /* write/print/format as SWI-Prolog lays terms out */\n' : '';
    const code = header + mode + swiMode + lib + '\n/* ---------- program ---------- */\n' + tables + natLib + protos.join('\n') + '\n' + natProtos + '\n\n' +
      (nDefs.length ? '/* native tier: DET predicates in the modes the queries use */\n' + nDefs.join('\n') + '\n' + natEntries.join('\n') + '\n' : '') +
      defs.join('\n') + '\n' + main;
    return { refs: [...refs.keys()].map(i => qs[i].text), code, warnings, proofs: [...new Set(proofNotes)] };
  }
  P.toC = toC;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
