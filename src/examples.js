(function(P){P.EXAMPLES=[
 {
  "id": "fib",
  "title": "Fibonacci: exponential Prolog, linear MNN Detlog",
  "src": "% Tree recursion: Prolog recomputes fib(N-2) inside fib(N-1).\n% MNN Detlog tables the pure predicate by call variant (rule MEMO)\n% and splices the two independent recursive calls (rule splice).\nfib(0, 0).\nfib(1, 1).\nfib(N, F) :-\n    N > 1,\n    N1 is N - 1,\n    N2 is N - 2,\n    fib(N1, F1),\n    fib(N2, F2),\n    F is F1 + F2.\n",
  "queries": [
   "fib(15, F)",
   "fib(10, F)"
  ],
  "sweep": "fib(N, F)",
  "values": "2..18 by 2"
 },
 {
  "id": "cuts",
  "title": "Cuts of several kinds",
  "src": "% Cuts of several kinds.  detlog2 turns each into an explicit decision.\n\n% a :- b, !, c.  a :- d.   becomes   a :- if_commit(b, c, d).\na(X) :- b(X), !, c(X).\na(X) :- d(X).\nb(1). b(2).\nc(1).\nd(3).\n\n% A red cut (meaning-changing) and a green one.\nmax(X, Y, X) :- X >= Y, !.\nmax(_, Y, Y).\n\nclassify(N, neg) :- N < 0, !.\nclassify(0, zero) :- !.\nclassify(_, pos).\n\n% First solution only, with a cut local to findall's goal.\nfirsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).\n\n% Two cuts in one clause.\ntwo(X, Y) :- member(X, [1, 2, 3]), X > 1, !, member(Y, [a, b]), !.\ntwo(none, none).\n\n% A cut inside \\+ is local to it.\nno_big(L) :- \\+ (member(X, L), X > 5, !).\n\n% \"!\" here is data (a character list), not a cut.\nbang(Out) :- append(\"Hi\", \"!\", Out).\n",
  "queries": [
   "a(X)",
   "max(5, 3, Z)",
   "max(1, 3, Z)",
   "classify(0, C)",
   "classify(-4, C)",
   "firsts([1,2,3], F)",
   "two(X, Y)",
   "no_big([1,2])",
   "no_big([7])"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "branchcut",
  "title": "A cut inside an if-then-else branch",
  "src": "% The cut in the then-branch cuts the whole clause: member/2's later\n% answers and pick/2's second clause.  Detlog writes it as a cut marker:\n% the row loop stops after it and the later clause is dropped.\npick(N, X) :- ( N > 3 -> member(X, [big, huge]), ! ; X = small ).\npick(_, other).\n\nfirst_over(L, Min, X) :- member(X, L), ( X > Min -> ! ; fail ).\nfirst_over(_, _, none).\n\nw(X) :- member(X, [1, 2, 3]), write(X), ( X >= 2 -> nl, ! ; true ).\nw(last).\n",
  "queries": [
   "pick(5, X)",
   "pick(2, X)",
   "first_over([1,5,9], 3, X)",
   "first_over([1,2], 3, X)",
   "w(X)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "splice",
  "title": "Splicing independent generators",
  "src": "% The splice example from the Detlog notes: two generators whose answers\n% are combined.  detlog2 computes each packet once and splices them:\n%   ?- c(A, B).   A = 1, B = 3 ; A = 1, B = 4 ; A = 2, B = 3 ; A = 2, B = 4.\n\nc(A, B) :- a(A), b(B).\na(A) :- member(A, [1, 2]).\nb(B) :- member(B, [3, 4]).\n\n% Three positions, one of them fixed: splice([fixed, cp([1,2]), x], Rows).\ntriple(X, Y, Z) :- X = fixed, member(Y, [1, 2]), Z = x.\n\n% A dependent conjunction: q/2 needs the answer of p/1.\np(1). p(2). p(3).\nq(X, Y) :- p(X), Y is X * 10, Y > 10.\n\n% a larger product: three independent generators\ndigit(D) :- between(0, 9, D).\npin(A, B, C) :- digit(A), digit(B), digit(C), A + B + C =:= 25.\n",
  "queries": [
   "c(A, B)",
   "triple(X, Y, Z)",
   "q(X, Y)",
   "pin(A, B, C)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "unfold",
  "title": "Data unfolded into S2A loops",
  "src": "/*  unfold.pl - data and the rules over it, for detlog2 unfold.\n\n    detlog2 unfold examples/unfold.pl -o out.pl --check 'step(X, 13)'\n\n    Every pure predicate is unfolded into its answer table, and each table\n    becomes an S2A loop.  first_colour/1 has a cut and evens/1 has infinitely\n    many answers, so they are converted as usual instead.\n*/\n\n% facts with a pattern: V = 3 + 5*I\nstep(0, 3).\nstep(1, 8).\nstep(2, 13).\nstep(3, 18).\nstep(4, 23).\n\n% data computed by rules\nsquare(N, S) :- between(0, 6, N), S is N * N.\ntriangle(N, T) :- between(0, 9, N), T is N * (N + 1) // 2.\ncube(N, C) :- between(0, 5, N), C is N * N * N - 2.\n\n% facts with no formula: the values are listed\ncolour(0, red).\ncolour(1, green).\ncolour(2, blue).\n\n% rules over the data, recursion included\npair(N, S, C) :- square(N, S), N < 3, colour(N, C).\ntwo_steps(X, Z) :- step(X, Y), step(Y, Z).\nparent(ann, bob).\nparent(bob, cy).\nparent(cy, dee).\nanc(X, Y) :- parent(X, Y).\nanc(X, Y) :- parent(X, Z), anc(Z, Y).\neither(X) :- ( X = 1 ; X = 2 ; X = 1 ).\n\n% not pure: converted, not unfolded (it calls colour/2's loop)\nfirst_colour(C) :- colour(_, C), !.\n\n% infinitely many answers: converted, not unfolded\nevens(X) :- between(0, inf, Y), X is 2 * Y.\n",
  "queries": [
   "step(X, 13)",
   "square(N, 25)",
   "triangle(N, T)",
   "cube(3, C)",
   "pair(N, S, C)",
   "two_steps(X, Z)",
   "anc(X, dee)",
   "either(X)",
   "first_colour(C)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "output",
  "title": "Output written from inside generators",
  "src": "% Output written from inside generators.  In converted code output is data\n% (out(Text) items of the answer packets), so it comes out in exactly the\n% order Prolog writes it.\n\ngen(X) :- member(X, [1, 2]), write(g(X)).\n\n% g(1)s(1)  then  g(2)s(2): the generator's output interleaves with the caller's\nshow :- gen(X), write(s(X)), nl, fail.\nshow.\n\n% two writing generators in one conjunction\npairs :- gen(X), gen(Y), write(X-Y), nl, fail.\npairs.\n\n% commitment stops output at the first answer\nfirst_big(X) :- once((member(X, [1, 5, 9]), write(try(X)), X > 3)).\n\n% output inside findall/3 and aggregate_all/3\ncount_out(N) :- aggregate_all(count, gen(_), N).\nlogged(L) :- findall(X, (gen(X), write(','), X > 0), L), nl.\n",
  "queries": [
   "show",
   "pairs",
   "first_big(X)",
   "count_out(N)",
   "logged(L)"
  ],
  "sweep": "",
  "values": ""
 },
 {
  "id": "lists",
  "title": "Lists, higher-order, aggregates, DCG",
  "src": "% a broader program\nnrev([], []).\nnrev([H|T], R) :- nrev(T, RT), app(RT, [H], R).\napp([], L, L).\napp([H|T], L, [H|R]) :- app(T, L, R).\nlen([], 0).\nlen([_|T], N) :- len(T, M), N is M + 1.\ndouble(X, Y) :- Y is 2 * X.\nadd(X, A0, A) :- A is A0 + X.\ndoubles(L, D) :- maplist(double, L, D).\ntotal(L, S) :- foldl(add, L, 0, S).\nscale(K, L, R) :- maplist([X, Y]>>(Y is K * X), L, R).\nsum_with(L, S) :- foldl([X, A0, A]>>(A is A0 + X), L, 0, S).\nsmall(L, S) :- exclude([X]>>(X > 2), L, S).\nsplit(L, I, E) :- partition(even, L, I, E).\nevens(L, E) :- include(even, L, E).\neven(X) :- 0 is X mod 2.\ncolour(red). colour(green). colour(blue).\nsize(small). size(large).\ncombo(C-S) :- colour(C), size(S).\ncount_combos(N) :- aggregate_all(count, combo(_), N).\nmax_len(M) :- aggregate_all(max(L), (colour(C), atom_length(C, L)), M).\nsorted(Cs) :- setof(C, colour(C), Cs).\ngreet(Name) :- format(\"hello ~w~n\", [Name]).\ngreet_all :- forall(colour(C), greet(C)).\nclassify(X, small) :- X < 10.\nclassify(X, big) :- X >= 10, X < 100.\nclassify(_, huge).\nfirst_class(X, C) :- once(classify(X, C)).\nnot_red(C) :- colour(C), \\+ C = red.\npath(a, b). path(b, c). path(c, d).\nreach(X, Y) :- path(X, Y).\nreach(X, Y) :- path(X, Z), reach(Z, Y).\ndigits([D|T]) --> digit(D), digits(T).\ndigits([D]) --> digit(D).\ndigit(D) --> [D], { code_type(D, digit) }.\nparse(S, N) :- atom_codes(S, Cs), phrase(digits(Ds), Cs), number_codes(N, Ds).\nalt(X) :- ( X = 1 ; X = 2 ; X = 3 ).\nnested(X, R) :- ( X > 0 -> ( X > 5 -> R = big ; R = small ) ; R = neg ).\nwords(S, W) :- split_string(S, \" \", \"\", Parts), length(Parts, W).\nhanoi(0, _, _, _) :- !.\nhanoi(N, A, B, C) :- N1 is N - 1, hanoi(N1, A, C, B), hanoi(N1, C, B, A).\nqueens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).\nsafe([]).\nsafe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).\nno_attack(_, [], _).\nno_attack(Q, [Q1|Qs], D) :- Q =\\= Q1 + D, Q =\\= Q1 - D, D1 is D + 1, no_attack(Q, Qs, D1).\n",
  "queries": [
   "nrev([1,2,3,4], R)",
   "app(X, Y, [a,b])",
   "doubles([1,2,3], D)",
   "total([1,2,3,4], S)",
   "scale(3, [1,2], R)",
   "evens([1,2,3,4,5,6], E)",
   "split([1,2,3,4], I, E)",
   "count_combos(N)",
   "sorted(Cs)",
   "greet_all",
   "not_red(C)",
   "reach(a, Y)",
   "parse('123', N)",
   "nested(7, R)",
   "words(\"a b c\", W)",
   "queens(5, Qs)"
  ],
  "sweep": "numlist(1, N, L), nrev(L, R)",
  "values": "4..40 by 4"
 },
 {
  "id": "queens",
  "title": "N-queens by generate and test",
  "src": "queens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).\nsafe([]).\nsafe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).\nno_attack(_, [], _).\nno_attack(Q, [Q1|Qs], D) :-\n    Q =\\= Q1 + D, Q =\\= Q1 - D,\n    D1 is D + 1,\n    no_attack(Q, Qs, D1).\n",
  "queries": [
   "queens(4, Qs)",
   "queens(6, Qs)"
  ],
  "sweep": "queens(N, Qs)",
  "values": "3..7"
 },
 {
  "id": "scan",
  "title": "First-match scans: committed member/2 conditions",
  "src": "% First-match scans (rules ite_scan and neg_scan).\n% A committed condition (member(X, Xs), Filters) becomes one recursive scan\n% that stops at the first element passing the filters, as Prolog does:\n% later elements are never tested, so they cannot raise errors.\n\n% A cut local to findall's goal.\nfirsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).\n\n% once/1, and an if-then-else with a real then-branch.\nfirst_big(L, X) :- once((member(X, L), X > 10)).\nlabel(L, R) :- ( member(X, L), X mod 2 =:= 0 -> R = even(X) ; R = none ).\n\n% \\+ is the same scan with T = fail and F = true.\nall_small(L) :- \\+ (member(X, L), X >= 10).\n\n% The element can be a pattern; a deterministic prefix runs once.\nkey_of(K, Pairs, V) :- once(member(K-V, Pairs)).\nabove(N, L, Y) :- ( M is N * 2, member(Y, L), Y > M -> true ; Y = none ).\n",
  "queries": [
   "firsts([0,3,5], F)",
   "firsts([2,a], F)",
   "first_big([3,20,x], X)",
   "label([1,4,6], R)",
   "label([1,3], R)",
   "all_small([1,2])",
   "all_small([1,12,a])",
   "key_of(b, [a-1,b-2,b-3], V)",
   "above(2, [1,5,9], Y)",
   "above(5, [1,5], Y)"
  ],
  "sweep": "",
  "values": ""
 }
];})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
