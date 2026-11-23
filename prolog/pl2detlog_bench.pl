/*  pl2detlog_bench.pl -- runs a query in a fresh process for pl2detlog_compile/2:
    its answer and output once, then its time per run.
*/
:- module(pl2detlog_bench, [bench/4]).

bench(File, GoalText, ResultFile, Budget) :-
    file_directory_name(File, Dir),
    working_directory(_, Dir),
    catch_halt,
    (   catch(load_files(user:File, [silent(true)]), E, true), var(E)
    ->  term_string(G, GoalText, [module(user)]),
        copy_term(G, G1),
        run(user:G1, R, Out, T0),
        (   R = halted(_) -> T1 = T0 ; time_reps(user:G, 1, T1) ),
        (   R = halted(_)
        ->  Reps = 1, Per = T0
        ;   T1 > Budget
        ->  Reps = 1, Per = T1
        ;   Reps is max(1, min(100000, floor(Budget / max(T1, 1.0e-6)))),
            time_reps(user:G, Reps, Per)
        ),
        write_result(ResultFile, result(R, Out, Reps, Per))
    ;   write_result(ResultFile, result(error(load), "", 0, 0))
    ),
    halt.

%   halt/0,1 called by the program end the run, not the process
catch_halt :-
    catch(( redefine_system_predicate(user:halt),
            redefine_system_predicate(user:halt(_)),
            assertz((user:halt :- throw(pl2detlog_halt(0)))),
            assertz((user:halt(S) :- throw(pl2detlog_halt(S)))) ),
          _, true).

run(G, R, Out, T) :-
    get_time(T0),
    with_output_to(string(Out),
                   catch(( call(G) -> R = true ; R = false ), E, err(E, R))),
    get_time(T2),
    T is T2 - T0.

err(pl2detlog_halt(S), halted(S)) :- !.
err(E, error(M)) :- message_to_codes(E, M).

message_to_codes(E, M) :-
    (   catch(message_to_codes_(E, M), _, fail) -> true ; format(string(M), "~q", [E]) ).
message_to_codes_(E, M) :- E = error(F, _), !, format(string(M), "~q", [F]).
message_to_codes_(E, M) :- format(string(M), "~q", [E]).

time_reps(G, Reps, Per) :-
    get_time(T0),
    forall(between(1, Reps, _),
           ( catch(abolish_all_tables, _, true),
             with_output_to(string(_), catch(( call(G) -> true ; true ), _, true)) )),
    get_time(T1),
    Per is (T1 - T0) / Reps.

write_result(F, T) :-
    setup_call_cleanup(open(F, write, S), ( writeq(S, T), write(S, '.\n') ), close(S)).
