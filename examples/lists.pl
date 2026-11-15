% a broader program
nrev([], []).
nrev([H|T], R) :- nrev(T, RT), app(RT, [H], R).
app([], L, L).
app([H|T], L, [H|R]) :- app(T, L, R).
len([], 0).
len([_|T], N) :- len(T, M), N is M + 1.
double(X, Y) :- Y is 2 * X.
add(X, A0, A) :- A is A0 + X.
doubles(L, D) :- maplist(double, L, D).
total(L, S) :- foldl(add, L, 0, S).
scale(K, L, R) :- maplist([X, Y]>>(Y is K * X), L, R).
sum_with(L, S) :- foldl([X, A0, A]>>(A is A0 + X), L, 0, S).
small(L, S) :- exclude([X]>>(X > 2), L, S).
split(L, I, E) :- partition(even, L, I, E).
evens(L, E) :- include(even, L, E).
even(X) :- 0 is X mod 2.
colour(red). colour(green). colour(blue).
size(small). size(large).
combo(C-S) :- colour(C), size(S).
count_combos(N) :- aggregate_all(count, combo(_), N).
max_len(M) :- aggregate_all(max(L), (colour(C), atom_length(C, L)), M).
sorted(Cs) :- setof(C, colour(C), Cs).
greet(Name) :- format("hello ~w~n", [Name]).
greet_all :- forall(colour(C), greet(C)).
classify(X, small) :- X < 10.
classify(X, big) :- X >= 10, X < 100.
classify(_, huge).
first_class(X, C) :- once(classify(X, C)).
not_red(C) :- colour(C), \+ C = red.
path(a, b). path(b, c). path(c, d).
reach(X, Y) :- path(X, Y).
reach(X, Y) :- path(X, Z), reach(Z, Y).
digits([D|T]) --> digit(D), digits(T).
digits([D]) --> digit(D).
digit(D) --> [D], { code_type(D, digit) }.
parse(S, N) :- atom_codes(S, Cs), phrase(digits(Ds), Cs), number_codes(N, Ds).
alt(X) :- ( X = 1 ; X = 2 ; X = 3 ).
nested(X, R) :- ( X > 0 -> ( X > 5 -> R = big ; R = small ) ; R = neg ).
words(S, W) :- split_string(S, " ", "", Parts), length(Parts, W).
hanoi(0, _, _, _) :- !.
hanoi(N, A, B, C) :- N1 is N - 1, hanoi(N1, A, C, B), hanoi(N1, C, B, A).
queens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).
safe([]).
safe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).
no_attack(_, [], _).
no_attack(Q, [Q1|Qs], D) :- Q =\= Q1 + D, Q =\= Q1 - D, D1 is D + 1, no_attack(Q, Qs, D1).
