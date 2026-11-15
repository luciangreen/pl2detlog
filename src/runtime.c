/* pl2detlog C runtime for Detlog: terms, unification with a trail, packets, builtins.
   Generated programs call one C function per Detlog predicate; there are no choicepoints:
   each call commits to the clause its first argument selects, and if_commit/3 is compiled to
   "mark the trail, run the condition, undo and take the else branch if it failed". BSD-3-Clause. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>
#include <ctype.h>

enum { T_VAR, T_ATOM, T_INT, T_FLT, T_STR, T_CMP };
typedef struct Term Term;
struct Term {
  int tag; int arity; const char *name; long long iv; double fv;
  Term *ref; Term **args; long id; Term *cp; long cpe;
};
static long dl_steps = 0, dl_step_limit = 200000000L, dl_decisions = 0, dl_var_id = 0, dl_memo_hits = 0;
static void dl_die(const char *m, const char *x) { fprintf(stderr, "Detlog runtime error: %s%s%s\n", m, x ? " " : "", x ? x : ""); exit(2); }
#define STEP() do { if (++dl_steps > dl_step_limit) dl_die("step limit exceeded", NULL); } while (0)

/* ---------- memory ---------- */
static char *arena = NULL; static size_t arena_left = 0;
static void *alloc(size_t n) {
  n = (n + 15) & ~(size_t)15;
  if (n > arena_left) { size_t sz = n > (1u << 22) ? n : (1u << 22); arena = (char *)malloc(sz); if (!arena) dl_die("out of memory", NULL); arena_left = sz; }
  void *p = arena; arena += n; arena_left -= n; return p;
}
static Term *new_term(int tag) { Term *t = (Term *)alloc(sizeof(Term)); memset(t, 0, sizeof(Term)); t->tag = tag; return t; }

/* ---------- atoms ---------- */
#define AH 8192
static Term *atab[AH];
static unsigned long hstr(const char *s) { unsigned long h = 5381; while (*s) h = h * 33 + (unsigned char)*s++; return h; }
static Term *mk_atom(const char *s) {
  unsigned long h = hstr(s) % AH;
  for (;;) { Term *t = atab[h]; if (!t) break; if (strcmp(t->name, s) == 0) return t; h = (h + 1) % AH; }
  Term *t = new_term(T_ATOM); char *c = (char *)alloc(strlen(s) + 1); strcpy(c, s); t->name = c; atab[h] = t; return t;
}
static const char *intern(const char *s) { return mk_atom(s)->name; }
static Term *NIL, *A_TRUE, *A_E, *A_OUT, *A_FOUND, *A_NONE, *A_MINUS, *A_DOT;
static Term *mk_int(long long v) { Term *t = new_term(T_INT); t->iv = v; return t; }
static Term *mk_flt(double v) { Term *t = new_term(T_FLT); t->fv = v; return t; }
static Term *mk_str(const char *s) { Term *t = new_term(T_STR); char *c = (char *)alloc(strlen(s) + 1); strcpy(c, s); t->name = c; return t; }
static Term *mk_var(void) { Term *t = new_term(T_VAR); t->id = ++dl_var_id; return t; }
static Term *mk_cmp(const char *f, int n, Term **a) {
  if (n == 0) return mk_atom(f);
  Term *t = new_term(T_CMP); t->name = f; t->arity = n; t->args = (Term **)alloc(sizeof(Term *) * n);
  memcpy(t->args, a, sizeof(Term *) * n); return t;
}
static Term *mk_cons(Term *h, Term *tl) { Term *a[2] = { h, tl }; return mk_cmp(A_DOT->name, 2, a); }
static Term *deref(Term *t) { while (t->tag == T_VAR && t->ref) t = t->ref; return t; }
static int is_cons(Term *t) { return t->tag == T_CMP && t->arity == 2 && t->name == A_DOT->name; }
static int is_nil(Term *t) { return t == NIL; }

/* ---------- growable arrays ---------- */
typedef struct { Term **v; size_t n, cap; } TV;
static void tv_push(TV *a, Term *x) { if (a->n == a->cap) { a->cap = a->cap ? a->cap * 2 : 16; a->v = (Term **)realloc(a->v, sizeof(Term *) * a->cap); } a->v[a->n++] = x; }
static Term *tv_list(TV *a) { Term *r = NIL; for (size_t i = a->n; i-- > 0;) r = mk_cons(a->v[i], r); return r; }
static int list_to_tv(Term *t, TV *out) { t = deref(t); while (is_cons(t)) { tv_push(out, t->args[0]); t = deref(t->args[1]); } return is_nil(t); }

/* ---------- trail ---------- */
static TV trail;
#define TR_TOP (trail.n)
static void bind(Term *v, Term *t) { v->ref = t; tv_push(&trail, v); }
static void undo(size_t m) { while (trail.n > m) trail.v[--trail.n]->ref = NULL; }

/* ---------- unify / compare / copy ---------- */
static int unify(Term *a, Term *b) {
  TV st = { 0 }; tv_push(&st, a); tv_push(&st, b); int ok = 1;
  while (st.n) {
    Term *y = deref(st.v[--st.n]), *x = deref(st.v[--st.n]);
    if (x == y) continue;
    if (x->tag == T_VAR) { bind(x, y); continue; }
    if (y->tag == T_VAR) { bind(y, x); continue; }
    if (x->tag != y->tag) { ok = 0; break; }
    if (x->tag == T_ATOM) { ok = 0; break; }
    if (x->tag == T_INT) { if (x->iv != y->iv) { ok = 0; break; } continue; }
    if (x->tag == T_FLT) { if (x->fv != y->fv) { ok = 0; break; } continue; }
    if (x->tag == T_STR) { if (strcmp(x->name, y->name)) { ok = 0; break; } continue; }
    if (x->name != y->name || x->arity != y->arity) { ok = 0; break; }
    for (int i = 0; i < x->arity; i++) { tv_push(&st, x->args[i]); tv_push(&st, y->args[i]); }
  }
  free(st.v); return ok;
}
static int rank(Term *t) { switch (t->tag) { case T_VAR: return 0; case T_INT: case T_FLT: return 1; case T_ATOM: return 3; case T_STR: return 4; default: return 5; } }
static int compare(Term *a, Term *b) {
  a = deref(a); b = deref(b); if (a == b) return 0;
  int ra = rank(a), rb = rank(b); if (ra != rb) return ra < rb ? -1 : 1;
  switch (a->tag) {
    case T_VAR: return a->id < b->id ? -1 : 1;
    case T_INT: case T_FLT: {
      double x = a->tag == T_INT ? (double)a->iv : a->fv, y = b->tag == T_INT ? (double)b->iv : b->fv;
      if (x != y) return x < y ? -1 : 1; if (a->tag != b->tag) return a->tag == T_FLT ? -1 : 1; return 0; }
    case T_ATOM: case T_STR: { int c = strcmp(a->name, b->name); return c < 0 ? -1 : c > 0; }
    default:
      if (a->arity != b->arity) return a->arity < b->arity ? -1 : 1;
      { int c = strcmp(a->name, b->name); if (c) return c < 0 ? -1 : 1; }
      for (int i = 0; i < a->arity; i++) { int c = compare(a->args[i], b->args[i]); if (c) return c; }
      return 0;
  }
}
static long copy_epoch = 0;
static Term *copy_rec(Term *t) {
  t = deref(t);
  if (t->tag == T_VAR) { if (t->cpe != copy_epoch) { t->cpe = copy_epoch; t->cp = mk_var(); } return t->cp; }
  if (t->tag != T_CMP) return t;
  if (is_cons(t)) {
    TV hs = { 0 }; Term *x = t;
    while (is_cons(x)) { tv_push(&hs, copy_rec(x->args[0])); x = deref(x->args[1]); }
    Term *r = copy_rec(x); for (size_t i = hs.n; i-- > 0;) r = mk_cons(hs.v[i], r); free(hs.v); return r;
  }
  Term **a = (Term **)alloc(sizeof(Term *) * t->arity);
  for (int i = 0; i < t->arity; i++) a[i] = copy_rec(t->args[i]);
  Term *r = new_term(T_CMP); r->name = t->name; r->arity = t->arity; r->args = a; return r;
}
static Term *copy_term(Term *t) { copy_epoch++; return copy_rec(t); }
static Term *resolve(Term *t) {
  t = deref(t);
  if (t->tag != T_CMP) return t;
  if (is_cons(t)) {
    TV hs = { 0 }; Term *x = t;
    while (is_cons(x)) { tv_push(&hs, resolve(x->args[0])); x = deref(x->args[1]); }
    Term *r = resolve(x); for (size_t i = hs.n; i-- > 0;) r = mk_cons(hs.v[i], r); free(hs.v); return r;
  }
  Term **a = (Term **)alloc(sizeof(Term *) * t->arity);
  for (int i = 0; i < t->arity; i++) a[i] = resolve(t->args[i]);
  Term *r = new_term(T_CMP); r->name = t->name; r->arity = t->arity; r->args = a; return r;
}
static int is_ground(Term *t) { t = deref(t); if (t->tag == T_VAR) return 0; if (t->tag == T_CMP) for (int i = 0; i < t->arity; i++) if (!is_ground(t->args[i])) return 0; return 1; }
static void term_vars(Term *t, TV *out) {
  t = deref(t);
  if (t->tag == T_VAR) { for (size_t i = 0; i < out->n; i++) if (out->v[i] == t) return; tv_push(out, t); return; }
  if (t->tag == T_CMP) for (int i = 0; i < t->arity; i++) term_vars(t->args[i], out);
}

/* ---------- strings ---------- */
typedef struct { char *s; size_t n, cap; } SB;
static void sb_putn(SB *b, const char *s, size_t n) { if (b->n + n + 1 > b->cap) { b->cap = (b->n + n + 1) * 2; b->s = (char *)realloc(b->s, b->cap); } memcpy(b->s + b->n, s, n); b->n += n; b->s[b->n] = 0; }
static void sb_puts(SB *b, const char *s) { sb_putn(b, s, strlen(s)); }
static void sb_putc(SB *b, char c) { sb_putn(b, &c, 1); }

/* ---------- printing (matches pl2detlog's JS printer) ---------- */
typedef struct { const char *n; int p; const char *type; } Op;
static const Op infix_ops[] = {
  {":-",1200,"xfx"},{"-->",1200,"xfx"},{";",1100,"xfy"},{"|",1100,"xfy"},{"->",1050,"xfy"},{"*->",1050,"xfy"},{",",1000,"xfy"},{":=",990,"xfx"},
  {"=",700,"xfx"},{"\\=",700,"xfx"},{"==",700,"xfx"},{"\\==",700,"xfx"},{"@<",700,"xfx"},{"@>",700,"xfx"},{"@=<",700,"xfx"},{"@>=",700,"xfx"},
  {"=..",700,"xfx"},{"is",700,"xfx"},{"=:=",700,"xfx"},{"=\\=",700,"xfx"},{"<",700,"xfx"},{">",700,"xfx"},{"=<",700,"xfx"},{">=",700,"xfx"},
  {">:<",700,"xfx"},{":<",700,"xfx"},{"as",700,"xfx"},{":",200,"xfy"},{"+",500,"yfx"},{"-",500,"yfx"},{"/\\",500,"yfx"},{"\\/",500,"yfx"},{"xor",500,"yfx"},
  {"*",400,"yfx"},{"/",400,"yfx"},{"//",400,"yfx"},{"rem",400,"yfx"},{"mod",400,"yfx"},{"div",400,"yfx"},{"<<",400,"yfx"},{">>",400,"yfx"},
  {"divmod",400,"yfx"},{"rdiv",400,"yfx"},{"**",200,"xfx"},{"^",200,"xfy"},{".",100,"yfx"},{NULL,0,NULL} };
static const Op prefix_ops[] = { {":-",1200,"fx"},{"?-",1200,"fx"},{"\\+",900,"fy"},{"?",500,"fx"},{"-",200,"fy"},{"+",200,"fy"},{"\\",200,"fy"},{"$",1,"fx"},
  {"dynamic",1150,"fx"},{"discontiguous",1150,"fx"},{"initialization",1150,"fx"},{"table",1150,"fx"},{NULL,0,NULL} };
static const Op *find_op(const Op *t, const char *n) { for (; t->n; t++) if (!strcmp(t->n, n)) return t; return NULL; }
static int is_symch(char c) { return c && strchr("+-*/\\^<>=~:.?@#&$", c) != NULL; }
static int atom_needs_quote(const char *n) {
  if (!strcmp(n, "[]") || !strcmp(n, "!") || !strcmp(n, ";") || !strcmp(n, "{}")) return 0;
  if (!strcmp(n, ",")) return 1;
  if (*n >= 'a' && *n <= 'z') { for (const char *p = n; *p; p++) if (!(*p == '_' || (*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') || (*p >= '0' && *p <= '9'))) return 1; return 0; }
  if (*n) { for (const char *p = n; *p; p++) if (!is_symch(*p)) return 1; return 0; }
  return 1;
}
static void put_atom(SB *b, const char *n, int q) {
  if (!q || !atom_needs_quote(n)) { sb_puts(b, n); return; }
  sb_putc(b, '\'');
  for (const char *p = n; *p; p++) { if (*p == '\\') sb_puts(b, "\\\\"); else if (*p == '\'') sb_puts(b, "\\'"); else if (*p == '\n') sb_puts(b, "\\n"); else if (*p == '\t') sb_puts(b, "\\t"); else sb_putc(b, *p); }
  sb_putc(b, '\'');
}
static void put_float(SB *b, double v) {
  char buf[64];
  if (isinf(v)) { sb_puts(b, v > 0 ? "inf" : "-inf"); return; }
  if (isnan(v)) { sb_puts(b, "nan"); return; }
  for (int p = 1; p <= 17; p++) { snprintf(buf, sizeof buf, "%.*g", p, v); if (strtod(buf, NULL) == v) break; }
  /* JS style exponent: 1e-7, 1e+21 */
  char *e = strchr(buf, 'e');
  if (e) { char mant[64], ex[16]; size_t ml = (size_t)(e - buf); memcpy(mant, buf, ml); mant[ml] = 0; int x = atoi(e + 1);
    if (x >= -6 && x < 21) { snprintf(buf, sizeof buf, "%.17g", v); /* fall back */ char tmp[64]; for (int p = 1; p <= 17; p++) { snprintf(tmp, sizeof tmp, "%.*f", p, v); if (strtod(tmp, NULL) == v) { strcpy(buf, tmp); break; } } }
    else { snprintf(ex, sizeof ex, "e%c%d", x < 0 ? '-' : '+', x < 0 ? -x : x); snprintf(buf, sizeof buf, "%s%s", mant, ex); } }
  sb_puts(b, buf);
  if (!strchr(buf, '.') && !strchr(buf, 'e') && !strchr(buf, 'n') && !strchr(buf, 'i')) sb_puts(b, ".0");
}
static void put_str_json(SB *b, const char *s) {
  sb_putc(b, '"');
  for (const unsigned char *p = (const unsigned char *)s; *p; p++) {
    if (*p == '"') sb_puts(b, "\\\""); else if (*p == '\\') sb_puts(b, "\\\\"); else if (*p == '\n') sb_puts(b, "\\n"); else if (*p == '\t') sb_puts(b, "\\t"); else if (*p == '\r') sb_puts(b, "\\r");
    else if (*p < 0x20) { char u[8]; snprintf(u, sizeof u, "\\u%04x", *p); sb_puts(b, u); } else sb_putc(b, (char)*p);
  }
  sb_putc(b, '"');
}
static TV show_vars;
static void show(SB *b, Term *t, int q, int maxp);
static void show_str(SB *b, Term *t, int q, int maxp) { show(b, t, q, maxp); }
static void show(SB *b, Term *t, int q, int maxp) {
  t = deref(t);
  char buf[64];
  switch (t->tag) {
    case T_VAR: { size_t i; for (i = 0; i < show_vars.n; i++) if (show_vars.v[i] == t) break; if (i == show_vars.n) tv_push(&show_vars, t);
      /* _A, _B, ... _Z, _AA ... as the JS printer names them */
      char nb[16]; int k = (int)i, l = 0; char tmp[16]; do { tmp[l++] = (char)('A' + k % 26); k = k / 26 - 1; } while (k >= 0);
      nb[0] = '_'; for (int j = 0; j < l; j++) nb[1 + j] = tmp[l - 1 - j]; nb[1 + l] = 0; sb_puts(b, nb); return; }
    case T_INT: snprintf(buf, sizeof buf, "%lld", t->iv); sb_puts(b, buf); return;
    case T_FLT: put_float(b, t->fv); return;
    case T_STR: if (q) put_str_json(b, t->name); else sb_puts(b, t->name); return;
    case T_ATOM: {
      const Op *io = find_op(infix_ops, t->name), *po = find_op(prefix_ops, t->name);
      int special = !strcmp(t->name, "[]") || !strcmp(t->name, "{}") || !strcmp(t->name, "!") || !strcmp(t->name, ";");
      if ((io || po) && maxp < 1200 && !special) { int p = io ? io->p : 0; if (po && po->p > p) p = po->p; if (p > maxp) { sb_putc(b, '('); put_atom(b, t->name, q); sb_putc(b, ')'); return; } }
      put_atom(b, t->name, q); return; }
    case T_CMP: break;
  }
  if (is_cons(t)) {
    sb_putc(b, '['); Term *x = t; int first = 1;
    while (is_cons(x)) { if (!first) sb_puts(b, ", "); first = 0; show(b, x->args[0], q, 999); x = deref(x->args[1]); }
    if (!is_nil(x)) { sb_putc(b, '|'); show(b, x, q, 999); }
    sb_putc(b, ']'); return;
  }
  if (!strcmp(t->name, "{}") && t->arity == 1) { sb_putc(b, '{'); show(b, t->args[0], q, 1200); sb_putc(b, '}'); return; }
  if (t->arity == 2) {
    const Op *op = find_op(infix_ops, t->name);
    if (op) {
      int p = op->p, lp = op->type[0] == 'y' ? p : p - 1, rp = op->type[2] == 'y' ? p : p - 1;
      SB l = { 0 }, r = { 0 }; show(&l, t->args[0], q, lp); show(&r, t->args[1], q, rp);
      if (!l.s) sb_puts(&l, ""); if (!r.s) sb_puts(&r, "");
      if (p > maxp) sb_putc(b, '(');
      if (!strcmp(t->name, ",")) { sb_puts(b, l.s); sb_puts(b, ", "); sb_puts(b, r.s); }
      else {
        const char *n = t->name;
        int spaced = (*n >= 'a' && *n <= 'z') || p >= 700 || !strcmp(n, "->") || !strcmp(n, ":-") || !strcmp(n, "-->") || !strcmp(n, ";") || !strcmp(n, "*->");
        if (spaced) { sb_puts(b, l.s); sb_putc(b, ' '); put_atom(b, n, q); sb_putc(b, ' '); sb_puts(b, r.s); }
        else {
          SB ft = { 0 }; put_atom(&ft, n, q);
          int glueR = is_symch(ft.s[ft.n - 1]) && (is_symch(r.s[0]) || (r.s[0] == '-' && r.s[1] >= '0' && r.s[1] <= '9'));
          int glueL = is_symch(ft.s[0]) && l.n && is_symch(l.s[l.n - 1]);
          sb_puts(b, l.s); if (glueL) sb_putc(b, ' '); sb_puts(b, ft.s); if (glueR) sb_putc(b, ' '); sb_puts(b, r.s); free(ft.s);
        }
      }
      if (p > maxp) sb_putc(b, ')');
      free(l.s); free(r.s); return;
    }
  }
  if (t->arity == 1) {
    const Op *op = find_op(prefix_ops, t->name);
    if (op) {
      int p = op->p, ap = !strcmp(op->type, "fy") ? p : p - 1;
      Term *a0 = deref(t->args[0]);
      SB as = { 0 }; show(&as, a0, q, ap); if (!as.s) sb_puts(&as, "");
      SB ft = { 0 }; put_atom(&ft, t->name, q);
      int need = (ft.s[0] >= 'a' && ft.s[0] <= 'z') || (ft.s[0] >= 'A' && ft.s[0] <= 'Z') || !strcmp(ft.s, "\\+") || (is_symch(ft.s[ft.n - 1]) && (is_symch(as.s[0]) || a0->tag == T_INT || a0->tag == T_FLT)) || as.s[0] == '(';
      if (p > maxp) sb_putc(b, '(');
      sb_puts(b, ft.s); if (need) sb_putc(b, ' '); sb_puts(b, as.s);
      if (p > maxp) sb_putc(b, ')');
      free(as.s); free(ft.s); return;
    }
  }
  put_atom(b, t->name, q); sb_putc(b, '(');
  for (int i = 0; i < t->arity; i++) { if (i) sb_puts(b, ", "); show(b, t->args[i], q, 999); }
  sb_putc(b, ')');
}
static char *show_term(Term *t, int q) { SB b = { 0 }; show(&b, t, q, 1200); if (!b.s) sb_puts(&b, ""); return b.s; }
/* text of an atom, string, number or code/char list */
static char *text_of(Term *t) {
  t = deref(t); SB b = { 0 }; sb_puts(&b, "");
  if (t->tag == T_ATOM || t->tag == T_STR) { sb_puts(&b, t->name); return b.s; }
  if (t->tag == T_INT || t->tag == T_FLT) { free(b.s); return show_term(t, 0); }
  TV xs = { 0 };
  if (list_to_tv(t, &xs)) { for (size_t i = 0; i < xs.n; i++) { Term *x = deref(xs.v[i]); if (x->tag == T_INT) { char c[8]; long long cp = x->iv; if (cp < 0x80) { c[0] = (char)cp; c[1] = 0; } else if (cp < 0x800) { c[0] = (char)(0xC0 | (cp >> 6)); c[1] = (char)(0x80 | (cp & 63)); c[2] = 0; } else { c[0] = (char)(0xE0 | (cp >> 12)); c[1] = (char)(0x80 | ((cp >> 6) & 63)); c[2] = (char)(0x80 | (cp & 63)); c[3] = 0; } sb_puts(&b, c); } else if (x->tag == T_ATOM) sb_puts(&b, x->name); else dl_die("text expected", NULL); } free(xs.v); return b.s; }
  dl_die("text expected", show_term(t, 1)); return NULL;
}

/* ---------- arithmetic ---------- */
typedef struct { int f; long long i; double d; } Num;
static double nd(Num x) { return x.f ? x.d : (double)x.i; }
static Num NI(long long v) { Num n = { 0, v, 0 }; return n; }
static Num NF(double v) { Num n = { 1, 0, v }; return n; }
static Num eval(Term *t);
static Num eval(Term *t) {
  t = deref(t);
  switch (t->tag) {
    case T_INT: return NI(t->iv);
    case T_FLT: return NF(t->fv);
    case T_VAR: dl_die("instantiation error in arithmetic", NULL);
    case T_ATOM:
      if (!strcmp(t->name, "pi")) return NF(M_PI); if (!strcmp(t->name, "e")) return NF(M_E);
      if (!strcmp(t->name, "inf") || !strcmp(t->name, "infinite")) return NF(INFINITY); if (!strcmp(t->name, "nan")) return NF(NAN);
      if (!strcmp(t->name, "max_tagged_integer")) return NI(9007199254740991LL);
      if (!strcmp(t->name, "random")) return NF((double)rand() / RAND_MAX);
      dl_die("not evaluable:", t->name);
    case T_STR: if (strlen(t->name) == 1) return NI((unsigned char)t->name[0]); dl_die("not evaluable string", t->name);
  }
  const char *f = t->name;
  if (is_cons(t) && is_nil(deref(t->args[1]))) return eval(t->args[0]);
  if (t->arity == 1) {
    Num a = eval(t->args[0]);
    if (!strcmp(f, "-")) return a.f ? NF(-a.d) : NI(-a.i);
    if (!strcmp(f, "+")) return a;
    if (!strcmp(f, "abs")) return a.f ? NF(fabs(a.d)) : NI(a.i < 0 ? -a.i : a.i);
    if (!strcmp(f, "sign")) return a.f ? NF(a.d > 0 ? 1 : a.d < 0 ? -1 : 0) : NI(a.i > 0 ? 1 : a.i < 0 ? -1 : 0);
    if (!strcmp(f, "sqrt")) return NF(sqrt(nd(a)));
    if (!strcmp(f, "sin")) return NF(sin(nd(a))); if (!strcmp(f, "cos")) return NF(cos(nd(a))); if (!strcmp(f, "tan")) return NF(tan(nd(a)));
    if (!strcmp(f, "asin")) return NF(asin(nd(a))); if (!strcmp(f, "acos")) return NF(acos(nd(a))); if (!strcmp(f, "atan")) return NF(atan(nd(a)));
    if (!strcmp(f, "exp")) return NF(exp(nd(a))); if (!strcmp(f, "log")) return NF(log(nd(a))); if (!strcmp(f, "log2")) return NF(log2(nd(a)));
    if (!strcmp(f, "float")) return NF(nd(a)); if (!strcmp(f, "integer")) return NI((long long)llround(nd(a)));
    if (!strcmp(f, "truncate")) return NI((long long)trunc(nd(a))); if (!strcmp(f, "round")) return NI((long long)llround(nd(a)));
    if (!strcmp(f, "ceiling")) return NI((long long)ceil(nd(a))); if (!strcmp(f, "floor")) return NI((long long)floor(nd(a)));
    if (!strcmp(f, "float_integer_part")) return NF(trunc(nd(a))); if (!strcmp(f, "float_fractional_part")) return NF(nd(a) - trunc(nd(a)));
    if (!strcmp(f, "\\")) return NI(~a.i); if (!strcmp(f, "succ")) return NI(a.i + 1);
    if (!strcmp(f, "msb")) { long long x = a.i; int m = -1; while (x) { x >>= 1; m++; } return NI(m); }
  } else if (t->arity == 2) {
    Num a = eval(t->args[0]), b = eval(t->args[1]); int fl = a.f || b.f;
    if (!strcmp(f, "+")) return fl ? NF(nd(a) + nd(b)) : NI(a.i + b.i);
    if (!strcmp(f, "-")) return fl ? NF(nd(a) - nd(b)) : NI(a.i - b.i);
    if (!strcmp(f, "*")) return fl ? NF(nd(a) * nd(b)) : NI(a.i * b.i);
    if (!strcmp(f, "/")) { if (!fl) { if (b.i == 0) dl_die("division by zero", NULL); if (a.i % b.i == 0) return NI(a.i / b.i); return NF((double)a.i / (double)b.i); } return NF(nd(a) / nd(b)); }
    if (!strcmp(f, "//")) { if (b.i == 0) dl_die("division by zero", NULL); return NI(a.i / b.i); }
    if (!strcmp(f, "div")) { if (b.i == 0) dl_die("division by zero", NULL); long long q = a.i / b.i; if ((a.i % b.i != 0) && ((a.i < 0) != (b.i < 0))) q--; return NI(q); }
    if (!strcmp(f, "mod")) { if (b.i == 0) dl_die("division by zero", NULL); long long m = a.i % b.i; if (m != 0 && ((m < 0) != (b.i < 0))) m += b.i; return NI(m); }
    if (!strcmp(f, "rem")) { if (b.i == 0) dl_die("division by zero", NULL); return NI(a.i % b.i); }
    if (!strcmp(f, "min")) return nd(a) <= nd(b) ? a : b;
    if (!strcmp(f, "max")) return nd(a) >= nd(b) ? a : b;
    if (!strcmp(f, "**")) { if (!fl && b.i >= 0) { long long r = 1; for (long long k = 0; k < b.i; k++) r *= a.i; return NI(r); } return NF(pow(nd(a), nd(b))); }
    if (!strcmp(f, "^")) { if (!fl) { if (b.i < 0) dl_die("^ with a negative exponent", NULL); long long r = 1; for (long long k = 0; k < b.i; k++) r *= a.i; return NI(r); } return NF(pow(nd(a), nd(b))); }
    if (!strcmp(f, "atan2") || !strcmp(f, "atan")) return NF(atan2(nd(a), nd(b)));
    if (!strcmp(f, ">>")) return NI(a.i >> b.i); if (!strcmp(f, "<<")) return NI(a.i << b.i);
    if (!strcmp(f, "/\\")) return NI(a.i & b.i); if (!strcmp(f, "\\/")) return NI(a.i | b.i); if (!strcmp(f, "xor")) return NI(a.i ^ b.i);
    if (!strcmp(f, "gcd")) { long long x = llabs(a.i), y = llabs(b.i); while (y) { long long r = x % y; x = y; y = r; } return NI(x); }
    if (!strcmp(f, "log")) return NF(log(nd(b)) / log(nd(a)));
  }
  dl_die("not evaluable:", f); return NI(0);
}
static Term *num_term(Num n) { return n.f ? mk_flt(n.d) : mk_int(n.i); }
static int num_cmp(Term *a, Term *b) { Num x = eval(a), y = eval(b); if (!x.f && !y.f) return x.i < y.i ? -1 : x.i > y.i; double p = nd(x), q = nd(y); return p < q ? -1 : p > q; }

/* ---------- builtins (deterministic) ---------- */
static Term *list_of_chars(const char *s, int codes) { TV v = { 0 }; const unsigned char *p = (const unsigned char *)s;
  while (*p) { int cp, n; if (*p < 0x80) { cp = *p; n = 1; } else if ((*p >> 5) == 6) { cp = ((*p & 31) << 6) | (p[1] & 63); n = 2; } else if ((*p >> 4) == 14) { cp = ((*p & 15) << 12) | ((p[1] & 63) << 6) | (p[2] & 63); n = 3; } else { cp = ((*p & 7) << 18) | ((p[1] & 63) << 12) | ((p[2] & 63) << 6) | (p[3] & 63); n = 4; }
    if (codes) tv_push(&v, mk_int(cp)); else { char c[5]; memcpy(c, p, n); c[n] = 0; tv_push(&v, mk_atom(c)); } p += n; }
  Term *r = tv_list(&v); free(v.v); return r; }
static size_t utf8_len(const char *s) { size_t n = 0; for (; *s; s++) if ((*s & 0xC0) != 0x80) n++; return n; }
static int bi_length_det(Term **a) {
  Term *l = deref(a[0]); long long n = 0;
  while (is_cons(l)) { n++; l = deref(l->args[1]); }
  if (is_nil(l)) return unify(a[1], mk_int(n));
  if (l->tag != T_VAR) return 0;
  Term *N = deref(a[1]); if (N->tag != T_INT) dl_die("length/2: infinite (both unbound)", NULL);
  if (N->iv < n) return 0; TV v = { 0 }; for (long long i = n; i < N->iv; i++) tv_push(&v, mk_var()); int ok = unify(l, tv_list(&v)); free(v.v); return ok;
}
static int sort_cmp(const void *x, const void *y) { return compare(*(Term **)x, *(Term **)y); }
static int bi_call(const char *k, Term **a); /* dispatch */
static int sum_list(Term *l, Term **out) { TV v = { 0 }; if (!list_to_tv(l, &v)) dl_die("list expected", NULL); Num s = NI(0);
  for (size_t i = 0; i < v.n; i++) { Num x = eval(v.v[i]); s = (s.f || x.f) ? NF(nd(s) + nd(x)) : NI(s.i + x.i); } free(v.v); *out = num_term(s); return 1; }

static int bi_call(const char *k, Term **a) {
  STEP();
#define K(s) (!strcmp(k, s))
  if (K("=/2")) return unify(a[0], a[1]);
  if (K("\\=/2")) { size_t m = TR_TOP; int r = unify(a[0], a[1]); undo(m); return !r; }
  if (K("==/2")) return compare(a[0], a[1]) == 0;
  if (K("\\==/2")) return compare(a[0], a[1]) != 0;
  if (K("@</2")) return compare(a[0], a[1]) < 0;
  if (K("@>/2")) return compare(a[0], a[1]) > 0;
  if (K("@=</2")) return compare(a[0], a[1]) <= 0;
  if (K("@>=/2")) return compare(a[0], a[1]) >= 0;
  if (K("compare/3")) { int c = compare(a[1], a[2]); return unify(a[0], mk_atom(c < 0 ? "<" : c > 0 ? ">" : "=")); }
  if (K("is/2")) return unify(a[0], num_term(eval(a[1])));
  if (K("=:=/2")) return num_cmp(a[0], a[1]) == 0;
  if (K("=\\=/2")) return num_cmp(a[0], a[1]) != 0;
  if (K("</2")) return num_cmp(a[0], a[1]) < 0;
  if (K(">/2")) return num_cmp(a[0], a[1]) > 0;
  if (K("=</2")) return num_cmp(a[0], a[1]) <= 0;
  if (K(">=/2")) return num_cmp(a[0], a[1]) >= 0;
  if (K("true/0")) return 1;
  if (K("fail/0") || K("false/0")) return 0;
  if (K("var/1")) return deref(a[0])->tag == T_VAR;
  if (K("nonvar/1")) return deref(a[0])->tag != T_VAR;
  if (K("atom/1")) return deref(a[0])->tag == T_ATOM;
  if (K("number/1")) { int g = deref(a[0])->tag; return g == T_INT || g == T_FLT; }
  if (K("integer/1")) return deref(a[0])->tag == T_INT;
  if (K("float/1")) return deref(a[0])->tag == T_FLT;
  if (K("atomic/1")) { int g = deref(a[0])->tag; return g != T_VAR && g != T_CMP; }
  if (K("compound/1")) return deref(a[0])->tag == T_CMP;
  if (K("callable/1")) { int g = deref(a[0])->tag; return g == T_ATOM || g == T_CMP; }
  if (K("string/1")) return deref(a[0])->tag == T_STR;
  if (K("is_list/1")) { TV v = { 0 }; int r = list_to_tv(a[0], &v); free(v.v); return r; }
  if (K("ground/1")) return is_ground(a[0]);
  if (K("copy_term/2")) return unify(a[1], copy_term(a[0]));
  if (K("functor/3")) { Term *t = deref(a[0]);
    if (t->tag == T_VAR) { Term *n = deref(a[2]), *f = deref(a[1]); if (n->iv == 0) return unify(t, f); TV v = { 0 }; for (long long i = 0; i < n->iv; i++) tv_push(&v, mk_var()); int r = unify(t, mk_cmp(f->name, (int)n->iv, v.v)); free(v.v); return r; }
    if (t->tag == T_CMP) return unify(a[1], mk_atom(t->name)) && unify(a[2], mk_int(t->arity));
    return unify(a[1], t) && unify(a[2], mk_int(0)); }
  if (K("arg/3")) { Term *n = deref(a[0]), *t = deref(a[1]); if (n->tag != T_INT) dl_die("arg/3 with unbound index needs builtin_rows", NULL); if (t->tag != T_CMP || n->iv < 1 || n->iv > t->arity) return 0; return unify(a[2], t->args[n->iv - 1]); }
  if (K("=../2")) { Term *t = deref(a[0]);
    if (t->tag == T_CMP) { TV v = { 0 }; tv_push(&v, mk_atom(t->name)); for (int i = 0; i < t->arity; i++) tv_push(&v, t->args[i]); int r = unify(a[1], tv_list(&v)); free(v.v); return r; }
    if (t->tag != T_VAR) return unify(a[1], mk_cons(t, NIL));
    TV v = { 0 }; if (!list_to_tv(a[1], &v)) dl_die("=..: list expected", NULL); Term *h = deref(v.v[0]); int r = v.n == 1 ? unify(t, h) : unify(t, mk_cmp(h->name, (int)v.n - 1, v.v + 1)); free(v.v); return r; }
  if (K("succ/2")) { Term *x = deref(a[0]); if (x->tag == T_INT) return unify(a[1], mk_int(x->iv + 1)); Term *y = deref(a[1]); if (y->iv <= 0) return 0; return unify(x, mk_int(y->iv - 1)); }
  if (K("plus/3")) { Term *x = deref(a[0]), *y = deref(a[1]), *z = deref(a[2]);
    if (x->tag == T_INT && y->tag == T_INT) return unify(z, mk_int(x->iv + y->iv)); if (x->tag == T_INT) return unify(y, mk_int(z->iv - x->iv)); return unify(x, mk_int(z->iv - y->iv)); }
  if (K("length/2")) return bi_length_det(a);
  if (K("reverse/2")) { TV v = { 0 }; if (!list_to_tv(a[0], &v)) return 0; Term *r = NIL; for (size_t i = 0; i < v.n; i++) r = mk_cons(v.v[i], r); free(v.v); return unify(a[1], r); }
  if (K("msort/2") || K("sort/2")) { TV v = { 0 }; if (!list_to_tv(a[0], &v)) dl_die("sort: list expected", NULL); qsort(v.v, v.n, sizeof(Term *), sort_cmp);
    if (K("sort/2")) { size_t o = 0; for (size_t i = 0; i < v.n; i++) if (!o || compare(v.v[o - 1], v.v[i])) v.v[o++] = v.v[i]; v.n = o; }
    int r = unify(a[1], tv_list(&v)); free(v.v); return r; }
  if (K("sum_list/2") || K("sumlist/2")) { Term *s; sum_list(a[0], &s); return unify(a[1], s); }
  if (K("max_list/2") || K("min_list/2")) { TV v = { 0 }; list_to_tv(a[0], &v); if (!v.n) return 0; Num m = eval(v.v[0]); int mx = K("max_list/2");
    for (size_t i = 1; i < v.n; i++) { Num x = eval(v.v[i]); if (mx ? nd(x) > nd(m) : nd(x) < nd(m)) m = x; } free(v.v); return unify(a[1], num_term(m)); }
  if (K("nth0/3") || K("nth1/3")) { Term *i = deref(a[0]); if (i->tag != T_INT) dl_die("nth: unbound index needs builtin_rows", NULL); TV v = { 0 }; list_to_tv(a[1], &v); long long k = i->iv - (K("nth1/3") ? 1 : 0); int r = k >= 0 && k < (long long)v.n && unify(a[2], v.v[k]); free(v.v); return r; }
  if (K("last/2")) { TV v = { 0 }; list_to_tv(a[0], &v); int r = v.n && unify(a[1], v.v[v.n - 1]); free(v.v); return r; }
  if (K("memberchk/2")) { Term *l = deref(a[1]); while (is_cons(l)) { size_t m = TR_TOP; if (unify(a[0], l->args[0])) return 1; undo(m); l = deref(l->args[1]); } return 0; }
  if (K("numlist/3")) { long long lo = eval(a[0]).i, hi = eval(a[1]).i; TV v = { 0 }; for (long long i = lo; i <= hi; i++) tv_push(&v, mk_int(i)); int r = unify(a[2], tv_list(&v)); free(v.v); return r; }
  if (K("atom_length/2") || K("string_length/2")) return unify(a[1], mk_int((long long)utf8_len(text_of(a[0]))));
  if (K("atom_codes/2") || K("atom_chars/2") || K("string_codes/2") || K("string_chars/2")) { Term *t = deref(a[0]); int codes = strstr(k, "codes") != NULL; int str = !strncmp(k, "string", 6);
    if (t->tag != T_VAR) return unify(a[1], list_of_chars(text_of(t), codes)); return unify(t, str ? mk_str(text_of(a[1])) : mk_atom(text_of(a[1]))); }
  if (K("char_code/2")) { Term *t = deref(a[0]); if (t->tag == T_ATOM) { Term *l = list_of_chars(t->name, 1); return unify(a[1], deref(l)->args[0]); } char c[2] = { (char)deref(a[1])->iv, 0 }; return unify(t, mk_atom(c)); }
  if (K("atom_number/2")) { Term *t = deref(a[0]); if (t->tag == T_VAR) return unify(t, mk_atom(show_term(a[1], 0))); char *s = text_of(t); char *e; long long iv = strtoll(s, &e, 10); if (*s && !*e) return unify(a[1], mk_int(iv)); double d = strtod(s, &e); if (*s && !*e) return unify(a[1], mk_flt(d)); return 0; }
  if (K("number_codes/2")) { Term *t = deref(a[0]); if (t->tag != T_VAR) return unify(a[1], list_of_chars(show_term(t, 0), 1)); char *s = text_of(a[1]); char *e; long long iv = strtoll(s, &e, 10); if (*s && !*e) return unify(t, mk_int(iv)); return unify(t, mk_flt(strtod(s, NULL))); }
  if (K("atom_string/2")) { Term *t = deref(a[0]); if (t->tag != T_VAR) return unify(a[1], mk_str(text_of(t))); return unify(t, mk_atom(text_of(a[1]))); }
  if (K("string_concat/3")) { SB b = { 0 }; sb_puts(&b, text_of(a[0])); sb_puts(&b, text_of(a[1])); return unify(a[2], mk_str(b.s)); }
  if (K("atomic_list_concat/2") || K("atomic_list_concat/3")) { TV v = { 0 }; list_to_tv(a[0], &v); SB b = { 0 }; sb_puts(&b, ""); const char *sep = K("atomic_list_concat/3") ? text_of(a[1]) : "";
    for (size_t i = 0; i < v.n; i++) { if (i) sb_puts(&b, sep); sb_puts(&b, text_of(v.v[i])); } free(v.v); return unify(a[K("atomic_list_concat/3") ? 2 : 1], mk_atom(b.s)); }
  if (K("upcase_atom/2") || K("downcase_atom/2")) { char *s = text_of(a[0]); for (char *p = s; *p; p++) *p = K("upcase_atom/2") ? (char)toupper((unsigned char)*p) : (char)tolower((unsigned char)*p); return unify(a[1], mk_atom(s)); }
  if (K("term_to_atom/2")) return unify(a[1], mk_atom(show_term(a[0], 1)));
  if (K("code_type/2")) { Term *c = deref(a[0]); int ch = c->tag == T_INT ? (int)c->iv : (unsigned char)c->name[0]; Term *ty = deref(a[1]); const char *tn = ty->name;
    if (!strcmp(tn, "digit") && ty->tag == T_CMP) return isdigit(ch) && unify(ty->args[0], mk_int(ch - '0'));
    if (!strcmp(tn, "digit")) return isdigit(ch) != 0; if (!strcmp(tn, "alpha")) return isalnum(ch) || ch == '_'; if (!strcmp(tn, "alnum")) return isalnum(ch) != 0;
    if (!strcmp(tn, "space") || !strcmp(tn, "white")) return isspace(ch) != 0; if (!strcmp(tn, "upper")) return isupper(ch) != 0; if (!strcmp(tn, "lower")) return islower(ch) != 0;
    if (!strcmp(tn, "punct")) return ispunct(ch) != 0; if (!strcmp(tn, "csym")) return isalnum(ch) || ch == '_'; if (!strcmp(tn, "csymf")) return isalpha(ch) || ch == '_'; return 0; }
  if (K("split_string/4")) { char *s = text_of(a[0]), *sep = text_of(a[1]), *pad = text_of(a[2]); TV parts = { 0 }; SB cur = { 0 }; sb_puts(&cur, "");
    for (char *p = s;; p++) { if (*p == 0 || (*sep && strchr(sep, *p))) { char *x = cur.s; size_t n = strlen(x); size_t i = 0; while (i < n && *pad && strchr(pad, x[i])) i++; while (n > i && *pad && strchr(pad, x[n - 1])) n--; x[n] = 0; tv_push(&parts, mk_str(x + i)); cur.s = NULL; cur.n = cur.cap = 0; sb_puts(&cur, ""); if (!*p) break; } else sb_putc(&cur, *p); }
    int r = unify(a[3], tv_list(&parts)); free(parts.v); return r; }
  if (K("throw/1")) dl_die("uncaught exception:", show_term(a[0], 1));
#undef K
  dl_die("builtin not available in the C runtime:", k); return 0;
}

/* ---------- output effects ---------- */
static void format_into(SB *b, const char *f, Term *args) {
  TV v = { 0 }; if (!list_to_tv(args, &v)) { tv_push(&v, args); } size_t ai = 0;
  for (const char *p = f; *p; p++) {
    if (*p != '~') { sb_putc(b, *p); continue; }
    p++; int n = -1; while (*p >= '0' && *p <= '9') { n = (n < 0 ? 0 : n * 10) + (*p - '0'); p++; }
    switch (*p) {
      case 'w': case 'p': { char *s = show_term(v.v[ai++], 0); sb_puts(b, s); free(s); break; }
      case 'q': { char *s = show_term(v.v[ai++], 1); sb_puts(b, s); free(s); break; }
      case 'a': case 's': sb_puts(b, text_of(v.v[ai++])); break;
      case 'd': { char t[32]; snprintf(t, sizeof t, "%lld", deref(v.v[ai++])->iv); sb_puts(b, t); break; }
      case 'f': { char t[64]; snprintf(t, sizeof t, "%.*f", n < 0 ? 6 : n, nd(eval(v.v[ai++]))); sb_puts(b, t); break; }
      case 'e': { char t[64]; snprintf(t, sizeof t, "%.*e", n < 0 ? 6 : n, nd(eval(v.v[ai++]))); sb_puts(b, t); break; }
      case 'n': { int k = n < 0 ? 1 : n; while (k--) sb_putc(b, '\n'); break; }
      case 'c': { int k = n < 0 ? 1 : n; while (k--) sb_putc(b, (char)deref(v.v[ai])->iv); ai++; break; }
      case '~': sb_putc(b, '~'); break;
      case 't': case '|': case '+': break;
      default: sb_putc(b, '~'); sb_putc(b, *p);
    }
  }
  free(v.v);
}
static int rt_effect_text(Term *g, Term *T) {
  STEP(); g = deref(g); SB b = { 0 }; sb_puts(&b, "");
  const char *f = g->name; int n = g->tag == T_CMP ? g->arity : 0; Term **a = g->args;
  if (!strcmp(f, "write") && n == 1) { char *s = show_term(a[0], 0); sb_puts(&b, s); }
  else if (!strcmp(f, "print") && n == 1) { char *s = show_term(a[0], 1); sb_puts(&b, s); }
  else if (!strcmp(f, "writeq") && n == 1) { char *s = show_term(a[0], 1); sb_puts(&b, s); }
  else if (!strcmp(f, "write_canonical") && n == 1) { char *s = show_term(a[0], 1); sb_puts(&b, s); }
  else if (!strcmp(f, "write_term") && n == 2) { char *s = show_term(a[0], 0); sb_puts(&b, s); }
  else if (!strcmp(f, "writeln") && n == 1) { char *s = show_term(a[0], 0); sb_puts(&b, s); sb_putc(&b, '\n'); }
  else if (!strcmp(f, "nl") && n == 0) sb_putc(&b, '\n');
  else if (!strcmp(f, "tab") && n == 1) { long long k = eval(a[0]).i; while (k-- > 0) sb_putc(&b, ' '); }
  else if (!strcmp(f, "put_char") && n == 1) sb_puts(&b, deref(a[0])->name);
  else if (!strcmp(f, "format") && n == 1) format_into(&b, text_of(a[0]), NIL);
  else if (!strcmp(f, "format") && n == 2) format_into(&b, text_of(a[0]), a[1]);
  else if (!strcmp(f, "format") && n == 3) format_into(&b, text_of(a[1]), a[2]);
  else if (!strcmp(f, "flush_output") && n == 0) { }
  else dl_die("effect_text: unsupported output builtin", f);
  return unify(T, mk_str(b.s));
}

/* ---------- packets ---------- */
static int is_out(Term *t) { t = deref(t); return t->tag == T_CMP && t->arity == 1 && t->name == A_OUT->name; }
static int is_row(Term *t) { t = deref(t); return t->tag == T_CMP && t->arity == 1 && t->name == A_E->name; }
static Term *A_CUT;
static TV items(Term *t) { TV v = { 0 }; if (!list_to_tv(t, &v)) dl_die("packet is not a proper list", NULL); return v; }
static int is_cut(Term *t) { return deref(t) == A_CUT; }
static int has_cut(TV *v) { for (size_t i = 0; i < v->n; i++) if (is_cut(v->v[i])) return 1; return 0; }
/* cut markers: rows_concat_cut keeps markers and stops after a list containing one; rows_cut_concat also strips them */
static int rt_concat_cut(Term *ls, Term *out, int strip) {
  TV L = items(ls), all = { 0 };
  for (size_t i = 0; i < L.n; i++) { TV x = items(L.v[i]); for (size_t j = 0; j < x.n; j++) { STEP(); if (!(strip && is_cut(x.v[j]))) tv_push(&all, x.v[j]); } int c = has_cut(&x); free(x.v); if (c) break; }
  int r = unify(out, tv_list(&all)); free(L.v); free(all.v); return r;
}
static int rt_rows_concat_cut(Term *ls, Term *out) { return rt_concat_cut(ls, out, 0); }
static int rt_rows_cut_concat(Term *ls, Term *out) { return rt_concat_cut(ls, out, 1); }
static int rt_strip_cut(Term *R, Term *out) { Term *l[1] = { R }; return rt_concat_cut(tv_list(&(TV){ l, 1, 1 }), out, 1); }
static int rt_cut_in(Term *I, Term *O) { if (!is_row(I)) return 0; TV x = items(O); int c = has_cut(&x); free(x.v); return c; }
static Term *mk_e(Term *x) { return mk_cmp(A_E->name, 1, &x); }
static Term *pair(Term *a, Term *b) { Term *x[2] = { a, b }; return mk_cmp(A_MINUS->name, 2, x); }
static int rt_rows_concat(Term *ls, Term *out) {
  TV L = items(ls), all = { 0 };
  for (size_t i = 0; i < L.n; i++) { TV x = items(L.v[i]); for (size_t j = 0; j < x.n; j++) { STEP(); tv_push(&all, x.v[j]); } free(x.v); }
  int r = unify(out, tv_list(&all)); free(L.v); free(all.v); return r;
}
static int rt_splice_extend(Term *P, Term *pat, Term *env, Term *O) {
  TV it = items(P), res = { 0 };
  for (size_t i = 0; i < it.n; i++) {
    STEP(); Term *x = deref(it.v[i]);
    if (is_out(x) || is_cut(x)) { tv_push(&res, x); continue; }
    Term *c = copy_term(pair(pat, env)); size_t m = TR_TOP;
    if (unify(c->args[0], x->args[0])) tv_push(&res, resolve(c->args[1]));
    undo(m);
  }
  int r = unify(O, tv_list(&res)); free(it.v); free(res.v); return r;
}
static int rt_project_rows(Term *R, Term *vs, Term *h, Term *Rows) {
  TV it = items(R), res = { 0 };
  for (size_t i = 0; i < it.n; i++) {
    STEP(); Term *x = deref(it.v[i]);
    if (is_out(x) || is_cut(x)) { tv_push(&res, x); continue; }
    Term *c = copy_term(pair(vs, h)); size_t m = TR_TOP;
    if (unify(c->args[0], x->args[0])) tv_push(&res, mk_e(resolve(c->args[1])));
    undo(m);
  }
  int r = unify(Rows, tv_list(&res)); free(it.v); free(res.v); return r;
}
static int rt_project_list(Term *R, Term *eg, Term *tg, Term *Ts) {
  TV it = items(R), res = { 0 };
  for (size_t i = 0; i < it.n; i++) {
    STEP(); Term *x = deref(it.v[i]); if (!is_row(x)) continue;
    Term *c = copy_term(pair(eg, tg)); size_t m = TR_TOP;
    if (unify(c->args[0], x)) tv_push(&res, resolve(c->args[1]));
    undo(m);
  }
  int r = unify(Ts, tv_list(&res)); free(it.v); free(res.v); return r;
}
static int rt_packet_first(Term *R, Term *Pre, Term *First) {
  TV it = items(R), pre = { 0 }; int r;
  for (size_t i = 0; i < it.n; i++) { STEP(); if (is_cut(it.v[i])) continue; if (is_out(it.v[i])) { tv_push(&pre, deref(it.v[i])); continue; }
    r = unify(Pre, tv_list(&pre)) && unify(First, mk_cons(it.v[i], NIL)); free(it.v); free(pre.v); return r; }
  r = unify(Pre, tv_list(&pre)) && unify(First, NIL); free(it.v); free(pre.v); return r;
}
static int rt_packet_split(Term *R, Term *Outs, Term *Rows) {
  TV it = items(R), o = { 0 }, w = { 0 };
  for (size_t i = 0; i < it.n; i++) { STEP(); if (is_cut(it.v[i])) continue; if (is_out(it.v[i])) tv_push(&o, deref(it.v[i])); else tv_push(&w, deref(it.v[i])); }
  int r = unify(Outs, tv_list(&o)) && unify(Rows, tv_list(&w)); free(it.v); free(o.v); free(w.v); return r;
}
static int rt_cp_filter(Term *F, Term *pat, Term *Rows) {
  TV it = items(F), res = { 0 };
  for (size_t i = 0; i < it.n; i++) {
    STEP(); Term *c = copy_term(pat); Term *f = copy_term(deref(it.v[i])->args[0]); size_t m = TR_TOP;
    if (unify(c, f)) tv_push(&res, mk_e(resolve(c)));
    undo(m);
  }
  int r = unify(Rows, tv_list(&res)); free(it.v); free(res.v); return r;
}
static int rt_aggregate_list(Term *S, Term *Ts, Term *R) {
  const char *sp = deref(S)->name; TV v = items(Ts); Term *r = NULL;
  if (!strcmp(sp, "count")) r = mk_int((long long)v.n);
  else if (!strcmp(sp, "sum")) sum_list(Ts, &r);
  else if (!strcmp(sp, "max") || !strcmp(sp, "min")) { if (!v.n) { free(v.v); return 0; } Num m = eval(v.v[0]); for (size_t i = 1; i < v.n; i++) { Num x = eval(v.v[i]); if (!strcmp(sp, "max") ? nd(x) > nd(m) : nd(x) < nd(m)) m = x; } r = num_term(m); }
  else if (!strcmp(sp, "bag")) r = Ts;
  else if (!strcmp(sp, "set")) { Term *a[2] = { Ts, mk_var() }; bi_call("sort/2", a); r = a[1]; }
  else dl_die("aggregate_list: unknown spec", sp);
  free(v.v); return unify(R, r);
}
static int rt_splice_safe(Term *A, Term *B) {
  TV va = { 0 }, vb = { 0 }; term_vars(A, &va); term_vars(B, &vb); int ok = 1;
  for (size_t i = 0; i < va.n && ok; i++) for (size_t j = 0; j < vb.n; j++) if (va.v[i] == vb.v[j]) { ok = 0; break; }
  free(va.v); free(vb.v); return ok;
}
static int rt_splice2(Term *PA, Term *PB, Term *pa, Term *pb, Term *env, Term *O) {
  TV A = items(PA), B = items(PB), res = { 0 };
  for (size_t i = 0; i < A.n; i++) {
    if (is_out(A.v[i])) { tv_push(&res, deref(A.v[i])); continue; }
    for (size_t j = 0; j < B.n; j++) {
      STEP(); if (is_out(B.v[j])) continue;
      Term *x[3] = { pa, pb, env }; Term *c = copy_term(mk_cmp(intern("f"), 3, x)); size_t m = TR_TOP;
      if (unify(c->args[0], deref(A.v[i])->args[0]) && unify(c->args[1], deref(B.v[j])->args[0])) tv_push(&res, resolve(c->args[2]));
      undo(m);
    }
  }
  int r = unify(O, tv_list(&res)); free(A.v); free(B.v); free(res.v); return r;
}
/* memo: variant key -> stored f(Args, Rows) */
typedef struct ME { char *key; Term *val; struct ME *next; } ME;
#define MH 65536
static ME *memo[MH];
static void vkey(SB *b, Term *t, TV *vs) {
  t = deref(t); char buf[64];
  switch (t->tag) {
    case T_VAR: { size_t i; for (i = 0; i < vs->n; i++) if (vs->v[i] == t) break; if (i == vs->n) tv_push(vs, t); snprintf(buf, sizeof buf, "_%zu ", i); sb_puts(b, buf); return; }
    case T_INT: snprintf(buf, sizeof buf, "i%lld ", t->iv); sb_puts(b, buf); return;
    case T_FLT: snprintf(buf, sizeof buf, "f%.17g ", t->fv); sb_puts(b, buf); return;
    case T_ATOM: sb_puts(b, "a"); sb_puts(b, t->name); sb_puts(b, "\x01"); return;
    case T_STR: sb_puts(b, "s"); sb_puts(b, t->name); sb_puts(b, "\x01"); return;
    default: sb_puts(b, "c"); sb_puts(b, t->name); snprintf(buf, sizeof buf, "/%d(", t->arity); sb_puts(b, buf); for (int i = 0; i < t->arity; i++) vkey(b, t->args[i], vs); sb_puts(b, ")"); return;
  }
}
static char *variant_key(Term *k, Term *args) { SB b = { 0 }; TV vs = { 0 }; vkey(&b, k, &vs); vkey(&b, args, &vs); free(vs.v); return b.s; }
static int rt_memo_lookup(Term *K, Term *Args, Term *Found) {
  STEP(); char *key = variant_key(K, Args); unsigned long h = hstr(key) % MH;
  for (ME *e = memo[h]; e; e = e->next) if (!strcmp(e->key, key)) {
    free(key); dl_memo_hits++;
    Term *c = copy_term(e->val); TV sv = { 0 }, cv = { 0 }; term_vars(c->args[0], &sv); term_vars(Args, &cv);
    for (size_t i = 0; i < sv.n && i < cv.n; i++) sv.v[i]->ref = cv.v[i];
    Term *r = resolve(c->args[1]); for (size_t i = 0; i < sv.n; i++) sv.v[i]->ref = NULL; free(sv.v); free(cv.v);
    return unify(Found, mk_cmp(A_FOUND->name, 1, &r));
  }
  free(key); return unify(Found, A_NONE);
}
static int rt_memo_store(Term *K, Term *Args, Term *Rows) {
  char *key = variant_key(K, Args); unsigned long h = hstr(key) % MH;
  for (ME *e = memo[h]; e; e = e->next) if (!strcmp(e->key, key)) { free(key); return 1; }
  ME *e = (ME *)malloc(sizeof(ME)); e->key = key; e->val = copy_term(pair(Args, Rows)); e->next = memo[h]; memo[h] = e; return 1;
}
static long long binom(long long n, int k) { double r = 1; for (int i = 0; i < k; i++) r = r * (double)(n - i) / (double)(i + 1); return llround(r); }
static int rt_s2a_rows(Term *spec, Term *args, Term *Rows) {
  spec = deref(spec); long long K = deref(spec->args[0])->iv; TV cols = items(spec->args[1]), as = items(args), res = { 0 };
  long long only = -2;
  for (size_t j = 0; j < cols.n; j++) { Term *c = deref(cols.v[j]), *x = deref(as.v[j]);
    if (!strcmp(c->name, "newton") && x->tag == T_INT) { TV ds = items(c->args[0]); if (ds.n == 2 && deref(ds.v[1])->iv != 0) { long long d0 = deref(ds.v[0])->iv, d1 = deref(ds.v[1])->iv; only = ((x->iv - d0) % d1 == 0 && (x->iv - d0) / d1 >= 0 && (x->iv - d0) / d1 < K) ? (x->iv - d0) / d1 : -1; free(ds.v); break; } free(ds.v); } }
  long long lo = 0, hi = K; if (only == -1) hi = 0; else if (only >= 0) { lo = only; hi = only + 1; }
  for (long long I = lo; I < hi; I++) {
    STEP(); TV row = { 0 };
    for (size_t j = 0; j < cols.n; j++) { Term *c = deref(cols.v[j]);
      if (!strcmp(c->name, "const")) tv_push(&row, c->args[0]);
      else if (!strcmp(c->name, "data")) { TV d = items(c->args[0]); tv_push(&row, d.v[I]); free(d.v); }
      else { TV ds = items(c->args[0]); long long s = 0; for (size_t d = 0; d < ds.n; d++) s += deref(ds.v[d])->iv * binom(I, (int)d); free(ds.v); tv_push(&row, mk_int(s)); } }
    Term *c = copy_term(args); size_t m = TR_TOP;
    if (unify(c, tv_list(&row))) tv_push(&res, mk_e(resolve(c)));
    undo(m); free(row.v);
  }
  int r = unify(Rows, tv_list(&res)); free(cols.v); free(as.v); free(res.v); return r;
}
/* nondeterministic builtins as packets: every answer of the builtin, in Prolog order */
static void row_of(TV *res, Term *g) { tv_push(res, mk_e(mk_cons(resolve(g), NIL))); }
static int rt_builtin_rows(Term *g, Term *P) {
  g = deref(g); TV res = { 0 }; const char *f = g->name; int n = g->arity; Term **a = g->args; size_t m = TR_TOP;
#define TRY(cond) do { STEP(); if (cond) row_of(&res, g); undo(m); } while (0)
  if (!strcmp(f, "member") && n == 2) { Term *l = deref(a[1]); while (is_cons(l)) { TRY(unify(a[0], l->args[0])); l = deref(l->args[1]); } if (l->tag == T_VAR) dl_die("member/2 on a partial list has no finite packet", NULL); }
  else if (!strcmp(f, "between") && n == 3) { long long lo = eval(a[0]).i; Term *hi = deref(a[1]); if (hi->tag == T_ATOM) dl_die("between/3 with inf has no finite packet", NULL); long long h = eval(hi).i; Term *x = deref(a[2]);
    if (x->tag == T_INT) { if (x->iv >= lo && x->iv <= h) row_of(&res, g); } else for (long long i = lo; i <= h; i++) TRY(unify(x, mk_int(i))); }
  else if (!strcmp(f, "append") && n == 3) { TV xs = { 0 };
    if (list_to_tv(a[0], &xs)) { Term *r = deref(a[1]); for (size_t i = xs.n; i-- > 0;) r = mk_cons(xs.v[i], r); TRY(unify(a[2], r)); }
    else { TV zs = { 0 }; if (!list_to_tv(a[2], &zs)) dl_die("append/3 with neither list proper has no finite packet", NULL);
      for (size_t i = 0; i <= zs.n; i++) { Term *pre = NIL; for (size_t j = i; j-- > 0;) pre = mk_cons(zs.v[j], pre); Term *suf = NIL; for (size_t j = zs.n; j-- > i;) suf = mk_cons(zs.v[j], suf); TRY(unify(a[0], pre) && unify(a[1], suf)); } free(zs.v); }
    free(xs.v); }
  else if (!strcmp(f, "select") && n == 3) { TV xs = { 0 }; if (!list_to_tv(a[1], &xs)) dl_die("select/3 needs a proper list", NULL);
    for (size_t i = 0; i < xs.n; i++) { Term *r = NIL; for (size_t j = xs.n; j-- > 0;) if (j != i) r = mk_cons(xs.v[j], r); TRY(unify(a[0], xs.v[i]) && unify(a[2], r)); } free(xs.v); }
  else if ((!strcmp(f, "nth0") || !strcmp(f, "nth1")) && n == 3) { int base = f[3] == '1'; TV xs = { 0 }; list_to_tv(a[1], &xs); Term *i0 = deref(a[0]);
    if (i0->tag == T_INT) { long long k = i0->iv - base; if (k >= 0 && k < (long long)xs.n) TRY(unify(a[2], xs.v[k])); }
    else for (size_t k = 0; k < xs.n; k++) TRY(unify(i0, mk_int((long long)k + base)) && unify(a[2], xs.v[k])); free(xs.v); }
  else if (!strcmp(f, "length") && n == 2) { TRY(bi_length_det(a)); }
  else if (!strcmp(f, "last") && n == 2) { TV xs = { 0 }; list_to_tv(a[0], &xs); if (xs.n) TRY(unify(a[1], xs.v[xs.n - 1])); free(xs.v); }
  else if (!strcmp(f, "arg") && n == 3) { Term *t = deref(a[1]); Term *k = deref(a[0]); if (t->tag == T_CMP) { if (k->tag == T_INT) { if (k->iv >= 1 && k->iv <= t->arity) TRY(unify(a[2], t->args[k->iv - 1])); } else for (int i = 0; i < t->arity; i++) TRY(unify(k, mk_int(i + 1)) && unify(a[2], t->args[i])); } }
  else if (!strcmp(f, "permutation") && n == 2) { TV xs = { 0 }; Term *src = a[0], *oth = a[1]; if (!list_to_tv(src, &xs)) { free(xs.v); xs.n = 0; src = a[1]; oth = a[0]; if (!list_to_tv(src, &xs)) dl_die("permutation/2 needs a proper list", NULL); }
    size_t k = xs.n; size_t *idx = (size_t *)calloc(k + 1, sizeof(size_t)); int *used = (int *)calloc(k + 1, sizeof(int)); long d = 0; idx[0] = 0;
    /* iterative depth-first enumeration in Prolog's order (select/3 based permutation) */
    TV cur = { 0 };
    for (;;) {
      if ((size_t)d == k) { TRY(unify(oth, tv_list(&cur))); d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }
      while (idx[d] < k && used[idx[d]]) idx[d]++;
      if (idx[d] >= k) { d--; if (d < 0) break; used[idx[d]] = 0; cur.n--; idx[d]++; continue; }
      used[idx[d]] = 1; tv_push(&cur, xs.v[idx[d]]); d++; idx[d] = 0;
    }
    free(idx); free(used); free(cur.v); free(xs.v); }
  else if (!strcmp(f, "atom_concat") && n == 3) { Term *x = deref(a[0]), *y = deref(a[1]);
    if (x->tag != T_VAR && y->tag != T_VAR) { SB b = { 0 }; sb_puts(&b, text_of(x)); sb_puts(&b, text_of(y)); TRY(unify(a[2], mk_atom(b.s))); }
    else { char *z = text_of(a[2]); size_t L = strlen(z); for (size_t i = 0; i <= L; i++) { if (i < L && (z[i] & 0xC0) == 0x80) continue; char *p = (char *)alloc(i + 1); memcpy(p, z, i); p[i] = 0; TRY(unify(x, mk_atom(p)) && unify(y, mk_atom(z + i))); } } }
  else if (!strcmp(f, "char_type") && n == 2) { Term *b2[2] = { a[0], a[1] }; TRY(bi_call("code_type/2", b2)); }
  else dl_die("builtin_rows: not available in the C runtime:", f);
#undef TRY
  int r = unify(P, tv_list(&res)); free(res.v); return r;
}
static int rt_unsupported(const char *what) { dl_die("predicate was not converted:", what); return 0; }

/* ---------- top level ---------- */
static void print_packet(Term *R, const char **names, int nv) {
  TV it = items(R); size_t rows = 0;
  for (size_t i = 0; i < it.n; i++) {
    Term *x = deref(it.v[i]);
    if (is_out(x)) { fputs(text_of(x->args[0]), stdout); continue; }
    if (x->tag != T_CMP) continue;
    rows++;
    TV vals = items(x->args[0]);
    show_vars.n = 0;
    if (!nv) puts("true");
    else { for (int j = 0; j < nv; j++) { char *s = show_term(vals.v[j], 1); printf("%s%s = %s", j ? ", " : "", names[j], s); free(s); } putchar('\n'); }
    free(vals.v);
  }
  if (!rows) puts("false");
  free(it.v);
}
static double now_ms(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6; }
static void rt_init(void) {
  NIL = mk_atom("[]"); A_TRUE = mk_atom("true"); A_E = mk_atom("e"); A_OUT = mk_atom("out");
  A_FOUND = mk_atom("found"); A_NONE = mk_atom("none"); A_MINUS = mk_atom("-"); A_DOT = mk_atom("."); A_CUT = mk_atom("cut");
}
/* first-argument selection test */
static int fa(Term *x, int tag, const char *name, int arity, long long iv) {
  x = deref(x); if (x->tag == T_VAR) return 1;
  if (tag < 0) return 1; /* clause head first argument is a variable */
  if (x->tag != tag) return 0;
  switch (tag) { case T_ATOM: return x->name == name; case T_INT: return x->iv == iv; case T_CMP: return x->name == name && x->arity == arity; default: return 1; }
}
/* ---------- end of runtime ---------- */
