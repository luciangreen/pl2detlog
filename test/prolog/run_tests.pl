/*  run_tests.pl -- tests of the SWI-Prolog module pl2detlog.pl

    swipl test/prolog/run_tests.pl            % run the 200 cases, compare with ios.txt
    swipl test/prolog/run_tests.pl --record   % run them and write ios.txt again

    Each case is a program and a query.  The query runs in all three forms (Prolog, Detlog,
    Detlog MNN), each in a fresh process; the case passes when all three give the same
    output and the same success, and that output is the one recorded in ios.txt (an
    input/output pair from a real run).  "all" cases print every answer, "first" cases
    print the first.
*/

:- initialization(main, main).

:- prolog_load_context(directory, D),
   atomic_list_concat([D, '/../../prolog/pl2detlog'], M),
   use_module(M).

:- prolog_load_context(directory, D), nb_setval(test_dir, D).

main(Argv) :-
    nb_getval(test_dir, D),
    atomic_list_concat([D, '/ios.txt'], IOs),
    atomic_list_concat([D, '/../../examples'], ExDir0),
    absolute_file_name(ExDir0, ExDir),
    atomic_list_concat([D, '/../../.pl2detlog_test_tmp'], Tmp0),
    absolute_file_name(Tmp0, Tmp),
    copy_examples(ExDir, Tmp),
    findall(N-C, ( cases(Cs), nth1(N, Cs, C) ), NCs),
    length(NCs, Total),
    maplist(run_case(Tmp), NCs, Lines),
    multi_folder_check(D, MultiOk0),
    no_query_check(Tmp, NQOk),
    ( MultiOk0 == true, NQOk == true -> MultiOk = true ; MultiOk = false ),
    (   memberchk('--record', Argv)
    ->  setup_call_cleanup(open(IOs, write, S),
                           forall(member(L, Lines), format(S, "~s~n", [L])), close(S)),
        format("recorded ~w cases in ~w~n", [Total, IOs]),
        include(failed_line, Lines, Bad), length(Bad, NB),
        ( NB =:= 0 -> halt(0) ; format("~w cases disagree between forms~n", [NB]), halt(1) )
    ;   read_lines(IOs, Old),
        compare_lines(Lines, Old, 0, Fails),
        Pass is Total - Fails,
        format("~w/~w cases pass~n", [Pass, Total]),
        ( Fails =:= 0, MultiOk == true -> halt(0) ; halt(1) )
    ).

%   multi/: a program in three folders.  The converted folders keep the same layout (so
%   include/use_module paths still work) and the program's output is the same in all forms.
multi_folder_check(D, Ok) :-
    atomic_list_concat([D, '/multi/app/main.pl'], Main),
    catch(pl2detlog_check(Main, [budget(0.0), quiet(true)], Rs), E, (print_message(error, E), Rs = [])),
    agree(Rs, Verdict, _),
    atomic_list_concat([D, '/multi'], M),
    findall(F, ( member(Form, [detlog, mnn]),
                 member(Rel, ['app/main.pl', 'lib/inventory.pl', 'lib/text/report.pl', 'detlog_rt.pl']),
                 format(atom(F), '~w/main_~w/~w', [M, Form, Rel]), \+ exists_file(F) ), Missing),
    (   Verdict == agree, Missing == []
    ->  Ok = true, format("multi-folder program: same output in all forms, folders mirrored~n")
    ;   Ok = false, format("FAIL multi-folder program: ~w, missing ~w~n", [Verdict, Missing])
    ).

%   every example converts with no query, and the converted program loads without errors
%   and answers the first example query as Prolog does
no_query_check(Tmp, Ok) :-
    findall(F, ( member(F, [fib, cuts, branchcut, splice, unfold, output, lists, queens, scan]),
                 \+ no_query_ok(Tmp, F) ), Bad),
    (   Bad == []
    ->  Ok = true, format("conversion with no query: all 9 examples load and answer as Prolog~n")
    ;   Ok = false, format("FAIL conversion with no query: ~w~n", [Bad])
    ).

no_query_ok(Tmp, F) :-
    atomic_list_concat([Tmp, '/', F, '.pl'], Path),
    once(example_query(F, Q)),
    term_string(G, Q, [variable_names(Vs)]),
    forall(member(Form, [detlog, mnn]),
           ( catch(pl2detlog_convert(Path, Form, [quiet(true)]), _, fail),
             format(atom(Out), '~w/~w_~w/~w.pl', [Tmp, F, Form, F]),
             answers_in(Path, G, Vs, A0), answers_in(Out, G, Vs, A1), A0 == A1 )).

answers_in(File, G, Vs, Answers) :-
    format(string(Q), "forall(~q, (print(~q), nl))", [G, Vs]),
    current_prolog_flag(executable, Exe),
    tmp_file(nq, T),
    format(string(Cmd), "'~w' -q -g ~q -t halt '~w' > '~w' 2>&1 < /dev/null", [Exe, Q, File, T]),
    shell(Cmd, _),
    read_file_to_string(T, Answers, []),
    delete_file(T).

copy_examples(From, To) :-
    ( exists_directory(To) -> true ; make_directory(To) ),
    directory_files(From, Fs),
    forall(( member(F, Fs), file_name_extension(_, pl, F) ),
           ( atomic_list_concat([From, '/', F], A), atomic_list_concat([To, '/', F], B),
             read_file_to_string(A, Str, []),
             setup_call_cleanup(open(B, write, S), write(S, Str), close(S)) )).

run_case(Tmp, N-case(File, Kind, Q), Line) :-
    atomic_list_concat([Tmp, '/', File, '.pl'], Path),
    test_query(Kind, Q, TQ),
    catch(pl2detlog_check(Path, [query(TQ), budget(0.0), quiet(true)], Rs),
          E, ( Rs = [], print_message(error, E) )),
    agree(Rs, Verdict, Out),
    format(string(Line), "~w ~w.pl ~w ~q => ~q ~w", [N, File, Kind, Q, Out, Verdict]),
    format("~s~n", [Line]),
    flush_output.

%   the query as run: print every answer, or the first
test_query(Kind, Q, TQ) :-
    term_string(T, Q, [variable_names(Vs0)]),
    exclude(underscore_name, Vs0, Vs),
    ( Vs == [] -> P = write(yes) ; P = print(Vs) ),
    (   Kind == all -> TQ = forall(T, (P, nl))
    ;   TQ = ((T -> P ; write(no)), nl)
    ).

underscore_name(N=_) :- sub_atom(N, 0, 1, _, '_').

agree(Rs, Verdict, Out) :-
    (   Rs = [r(prolog, _, _, P, _)|Others], P = R-Out0
    ->  Out = R-Out0,
        (   forall(member(r(_, _, _, X, _), Others), X == P)
        ->  Verdict = agree
        ;   findall(F, ( member(r(F, _, _, X, _), Others), X \== P ), Fs),
            format(atom(Verdict), 'DIFFERENT:~w', [Fs])
        )
    ;   Out = none, Verdict = 'DIFFERENT:no_result'
    ).

failed_line(L) :- sub_string(L, _, _, _, "DIFFERENT").

read_lines(F, Ls) :-
    (   exists_file(F)
    ->  read_file_to_string(F, S, []), split_string(S, "\n", "", Ls0), exclude(==(""), Ls0, Ls)
    ;   Ls = []
    ).

compare_lines([], _, F, F).
compare_lines([L|Ls], Old, F0, F) :-
    (   memberchk(L, Old), \+ failed_line(L) -> F1 = F0
    ;   format("FAIL: ~s~n", [L]), F1 is F0 + 1
    ),
    compare_lines(Ls, Old, F1, F).

%   The 63 example queries of the app, each as "all" and "first", and 74 value sweeps.
cases(Cs) :-
    findall(case(F, K, Q), ( example_query(F, Q), member(K, [all, first]) ), Cs1),
    findall(case(fib, first, Q), ( between(0, 24, N), format(atom(Q), 'fib(~w, F)', [N]) ), Cs2),
    findall(case(lists, first, Q),
            ( between(0, 19, N), format(atom(Q), 'numlist(1, ~w, L), nrev(L, R)', [N]) ), Cs3),
    findall(case(queens, first, Q),
            ( between(1, 8, N), format(atom(Q), 'aggregate_all(count, queens(~w, _), C)', [N]) ),
            Cs4),
    findall(case(cuts, all, Q), ( between(-3, 11, N), format(atom(Q), 'classify(~w, C)', [N]) ),
            Cs5),
    findall(case(lists, first, Q),
            ( member(N, [10, 100, 500, 1000, 2000, 5000]),
              format(atom(Q), 'numlist(1, ~w, _L), doubles(_L, _D), total(_D, S)', [N]) ), Cs6),
    append([Cs1, Cs2, Cs3, Cs4, Cs5, Cs6], Cs).

example_query(fib, 'fib(15, F)').
example_query(fib, 'fib(10, F)').
example_query(cuts, Q) :- member(Q, ['a(X)', 'a(3)', 'max(5, 3, Z)', 'max(1, 3, Z)',
    'classify(0, C)', 'classify(-4, C)', 'firsts([1,2,3], F)', 'two(X, Y)', 'no_big([1,2])',
    'no_big([7])']).
example_query(branchcut, Q) :- member(Q, ['pick(5, X)', 'pick(2, X)',
    'first_over([1,5,9], 3, X)', 'first_over([1,2], 3, X)', 'w(X)']).
example_query(splice, Q) :- member(Q, ['c(A, B)', 'triple(X, Y, Z)', 'q(X, Y)', 'pin(A, B, C)']).
example_query(unfold, Q) :- member(Q, ['step(X, 13)', 'square(N, 25)', 'triangle(N, T)',
    'cube(3, C)', 'pair(N, S, C)', 'two_steps(X, Z)', 'anc(X, dee)', 'either(X)',
    'first_colour(C)']).
example_query(output, Q) :- member(Q, ['show', 'pairs', 'first_big(X)', 'count_out(N)',
    'logged(L)']).
example_query(lists, Q) :- member(Q, ['nrev([1,2,3,4], R)', 'app(X, Y, [a,b])',
    'doubles([1,2,3], D)', 'total([1,2,3,4], S)', 'scale(3, [1,2], R)',
    'evens([1,2,3,4,5,6], E)', 'split([1,2,3,4], I, E)', 'count_combos(N)', 'sorted(Cs)',
    'greet_all', 'not_red(C)', 'reach(a, Y)', 'parse(\'123\', N)', 'nested(7, R)',
    'words("a b c", W)', 'queens(5, Qs)']).
example_query(queens, Q) :- member(Q, ['queens(4, Qs)', 'queens(6, Qs)']).
example_query(scan, Q) :- member(Q, ['firsts([0,3,5], F)', 'firsts([2,a], F)',
    'first_big([3,20,x], X)', 'label([1,4,6], R)', 'label([1,3], R)', 'all_small([1,2])',
    'all_small([1,12,a])', 'key_of(b, [a-1,b-2,b-3], V)', 'above(2, [1,5,9], Y)',
    'above(5, [1,5], Y)']).
