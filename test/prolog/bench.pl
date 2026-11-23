/*  bench.pl -- time the three forms on a few queries: swipl test/prolog/bench.pl

    Each query runs in a fresh process per form (pl2detlog_check/3), after a check that
    its output is Prolog's.  Prints a Markdown table of microseconds per run.
*/

:- initialization(main, main).

:- prolog_load_context(directory, D),
   atomic_list_concat([D, '/../../prolog/pl2detlog'], M),
   use_module(M),
   nb_setval(bench_dir, D).

query(fib, "fib(21, F), print(F), nl").
query(fib, "fib(25, F), print(F), nl").
query(lists, "numlist(1, 300, L), nrev(L, R), print(R), nl").
query(lists, "numlist(1, 2000, L), doubles(L, D), total(D, S), print(S), nl").
query(queens, "queens(8, Qs), print(Qs), nl").
query(queens, "forall(queens(6, Qs), (print(Qs), nl))").
query(splice, "forall(pin(A, B, C), (print(A-B-C), nl))").
query(unfold, "forall(anc(X, dee), (print(X), nl))").

main(_) :-
    nb_getval(bench_dir, D),
    atomic_list_concat([D, '/../../.pl2detlog_bench_tmp'], T0), absolute_file_name(T0, T),
    atomic_list_concat([D, '/../../examples'], E0), absolute_file_name(E0, E),
    ( exists_directory(T) -> true ; make_directory(T) ),
    format("| query | Prolog us | Detlog us | Detlog MNN us | MNN / Prolog | fastest |~n"),
    format("| --- | ---: | ---: | ---: | ---: | --- |~n"),
    forall(query(F, Q), row(E, T, F, Q)).

row(E, T, F, Q) :-
    atomic_list_concat([E, '/', F, '.pl'], Src),
    atomic_list_concat([T, '/', F, '.pl'], Dst),
    read_file_to_string(Src, S, []),
    setup_call_cleanup(open(Dst, write, O), write(O, S), close(O)),
    pl2detlog_check(Dst, [query(Q), budget(0.5), quiet(true)], Rs),
    memberchk(r(prolog, _, _, Ref, TP), Rs),
    memberchk(r(detlog, _, _, RD, TD), Rs),
    memberchk(r(mnn, _, _, RM, TM), Rs),
    ( RD == Ref, RM == Ref -> true ; format(user_error, "outputs differ: ~w~n", [Q]) ),
    Ratio is TM / TP,
    foldl(best, [detlog-TD, mnn-TM], prolog-TP, Best-_),
    us(TP, A), us(TD, B), us(TM, C),
    format("| `~w` | ~w | ~w | ~w | ~2f | ~w |~n", [Q, A, B, C, Ratio, Best]).

best(F-T, _-T0, F-T) :- T < T0, !.
best(_, B, B).

us(T, A) :- U is T * 1000000, ( U >= 100 -> format(atom(A), '~0f', [U]) ; format(atom(A), '~1f', [U]) ).
