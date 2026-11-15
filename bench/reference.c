/* reference.c - the example algorithms written directly in C, as a C programmer would write them.
   Each is the same algorithm as the Prolog source: no memoisation, no pruning, no different data structure.
   Lists are linked cells from a bump allocator (as a garbage-collected heap allocates).  Each benchmark
   is run repeatedly and timed in-process; it prints  name<TAB>microseconds-per-run<TAB>check-value.

   cc -O2 -o reference reference.c && ./reference */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef struct cell { long head; struct cell *tail; } cell;
static cell *heap; static size_t hp, hcap;
static cell *cons(long h, cell *t) { if (hp == hcap) { fprintf(stderr, "heap\n"); exit(1); } cell *c = &heap[hp++]; c->head = h; c->tail = t; return c; }
static double now_us(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec * 1e6 + ts.tv_nsec / 1e3; }
static volatile long sink;

/* fib(N, F): fib(0,0). fib(1,1). fib(N,F) :- N > 1, fib(N-1), fib(N-2). */
static long fib(long n) { if (n == 0) return 0; if (n == 1) return 1; return fib(n - 1) + fib(n - 2); }

/* nrev([],[]). nrev([H|T],R) :- nrev(T,RT), app(RT,[H],R).   app([],L,L). app([H|T],L,[H|R]) :- app(T,L,R). */
static cell *app(cell *a, cell *l) { if (!a) return l; return cons(a->head, app(a->tail, l)); }
static cell *nrev(cell *l) { if (!l) return NULL; return app(nrev(l->tail), cons(l->head, NULL)); }
static cell *numlist(long lo, long hi) { cell *r = NULL; for (long i = hi; i >= lo; i--) r = cons(i, r); return r; }

/* doubles(L, D) :- maplist(double, L, D).  total(L, S) :- foldl(add, L, 0, S). */
static cell *doubles(cell *l) { if (!l) return NULL; return cons(2 * l->head, doubles(l->tail)); }
static long total(cell *l) { long s = 0; for (; l; l = l->tail) s += l->head; return s; }

/* queens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).  All solutions, in Prolog's order:
   permutation/2 of SWI-Prolog selects each element in turn (select/3) and permutes the rest. */
static int no_attack(long q, const long *qs, int n, long d) { for (int i = 0; i < n; i++, d++) if (q == qs[i] + d || q == qs[i] - d) return 0; return 1; }
static int safe(const long *qs, int n) { for (int i = 0; i < n; i++) if (!no_attack(qs[i], qs + i + 1, n - i - 1, 1)) return 0; return 1; }
static long sols; static long solbuf[64][16];
static void perm(long *rest, int nrest, long *out, int k, int n) {
  if (nrest == 0) { if (safe(out, n)) { for (int i = 0; i < n; i++) solbuf[sols & 63][i] = out[i]; sols++; } return; }
  for (int i = 0; i < nrest; i++) {
    long x = rest[i], tmp[16]; int m = 0;
    for (int j = 0; j < nrest; j++) if (j != i) tmp[m++] = rest[j];
    out[k] = x; perm(tmp, m, out, k + 1, n);
  }
}
static long queens(int n) { long ns[16], out[16]; for (int i = 0; i < n; i++) ns[i] = i + 1; sols = 0; perm(ns, n, out, 0, n); return sols; }

/* digit(D) :- between(0, 9, D).  pin(A,B,C) :- digit(A), digit(B), digit(C), A+B+C =:= 25.  All solutions. */
static long pin(void) { long n = 0, acc = 0; for (long a = 0; a <= 9; a++) for (long b = 0; b <= 9; b++) for (long c = 0; c <= 9; c++) if (a + b + c == 25) { n++; acc += a * 100 + b * 10 + c; } sink = acc; return n; }

/* parent facts; anc(X,Y) :- parent(X,Y).  anc(X,Y) :- parent(X,Z), anc(Z,Y).  Query anc(X, dee): all X. */
static const int par[][2] = { {0, 1}, {1, 2}, {2, 3} };   /* ann=0 bob=1 cy=2 dee=3 */
static int ancs[16], nanc;
/* the number of answers of anc(Z, Y) with both bound: clause 1, then clause 2 */
static int anc_bb(int z, int y) { int n = 0; for (int i = 0; i < 3; i++) if (par[i][0] == z && par[i][1] == y) n++;
  for (int i = 0; i < 3; i++) if (par[i][0] == z) n += anc_bb(par[i][1], y); return n; }
/* anc(X, Y) with Y bound: every X, in Prolog's answer order */
static void anc(int y) { for (int i = 0; i < 3; i++) if (par[i][1] == y) ancs[nanc++] = par[i][0];
  for (int i = 0; i < 3; i++) for (int k = anc_bb(par[i][1], y); k > 0; k--) ancs[nanc++] = par[i][0]; }

#define BENCH(name, reps, body, check) do { double t0 = now_us(); for (long rep_ = 0; rep_ < (reps); rep_++) { hp = 0; body; } double t = (now_us() - t0) / (reps); printf("%s\t%.4f\t%ld\n", name, t, (long)(check)); } while (0)

int main(void) {
  hcap = 1 << 22; heap = malloc(hcap * sizeof(cell));
  long f; BENCH("fib(18, F)", 2000, f = fib(18), f);
  BENCH("fib(21, F)", 500, f = fib(21), f);
  cell *r; BENCH("numlist(1, 60, L), nrev(L, R)", 20000, r = nrev(numlist(1, 60)), r->head);
  BENCH("numlist(1, 300, L), nrev(L, R)", 500, r = nrev(numlist(1, 300)), r->head);
  long s; BENCH("numlist(1, 2000, L), doubles(L, D), total(D, S)", 5000, s = total(doubles(numlist(1, 2000))), s);
  long q; BENCH("queens(6, Qs)", 2000, q = queens(6), q);
  BENCH("queens(7, Qs)", 300, q = queens(7), q);
  long p; BENCH("pin(A, B, C)", 200000, p = pin(), p);
  BENCH("anc(X, dee)", 2000000, (nanc = 0, anc(3)), nanc);
  return 0;
}
