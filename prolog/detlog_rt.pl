/*  detlog_rt.pl -- the Detlog runtime for code written by pl2detlog.pl

    Converted files load it with  :- use_module(library(detlog_rt)).
    (or with a relative path, as pl2detlog writes it).

    Detlog code has no cut, no ;, no ->, no \+, no findall/3 and no call/N in the program.
    if_commit/3 is its one decision construct: it takes the first answer of a deterministic
    condition and runs Then, or runs Else when the condition has no answer.  When this library
    is loaded, if_commit/3 is compiled inline as (C -> T ; E), so it costs nothing at run time.

    Answer streams.  A nondeterministic predicate p/N is written as p__k(A1, ..., AN, K): it
    passes each answer, in Prolog's order, to the continuation K and succeeds, keeping the
    bindings, at the first answer that K accepts.  A rejected answer is undone by if_commit/3
    (the trail), so no answer is copied and no list of answers is built.  Continuations are
    terms; dl_k/1 applies one.  Its clauses are written by pl2detlog next to the code that
    makes the continuation (multifile), and dispatch on the continuation's name by
    first-argument indexing, so there is no call/N.
*/

:- module(detlog_rt,
          [ if_commit/3,
            dl_k/1,              % +K: run a continuation
            dl_gen_k/2,          % +Generator, +K: the answers of a builtin generator, lazily
            dl_select_k/4,       % +List, ?X, ?Rest, +K: select/3's answers, lazily
            dl_match_k/3,        % +Facts, +Call, +K: facts as data, lazily
            dl_findall_k/2,      % +StreamGoal, -List: the answers collected by dl_collect/1
            dl_findall_k/3,      % +StreamGoal, -List, ?Tail
            dl_aggregate_k/3,    % +Spec, +StreamGoal, -Result
            dl_aggregate/3,      % +Spec, +Values, -Result
            dl_solve_between/4,  % +Lo, +Hi, +Expr, -X: the X in Lo..Hi with X =:= Expr
            dl_once/1,           % +Goal: the first answer of a builtin goal
            dl_member/2          % ?X, +Answers: the boundary to backtracking Prolog
          ]).

:- multifile user:goal_expansion/2.
:- dynamic user:goal_expansion/2.
user:goal_expansion(if_commit(C, T, E), (C -> T ; E)).

:- meta_predicate if_commit(0, 0, 0), dl_once(0), dl_gen_k(0, +),
                  dl_findall_k(0, -), dl_findall_k(0, -, ?), dl_aggregate_k(+, 0, -).

%!  if_commit(:Cond, :Then, :Else)
%   The Detlog decision: the first answer of Cond selects Then, no answer selects Else.

if_commit(C, T, E) :- ( call(C) -> call(T) ; call(E) ).

%!  dl_k(+K)
%   Run the continuation K.  true accepts every answer; dl_collect(T) adds a copy of T to
%   the innermost dl_findall_k/2,3 and rejects the answer, so the producer goes on to the
%   next one.  pl2detlog adds a clause for each continuation it writes.

:- multifile dl_k/1.
:- discontiguous dl_k/1.

dl_k(true).
dl_k(dl_collect(T)) :- '$add_findall_bag'(T).          % fails

%!  dl_findall_k(+StreamGoal, -List)
%!  dl_findall_k(+StreamGoal, -List, ?Tail)
%   List are the copies that StreamGoal's dl_collect/1 continuation collected, in order.
%   This is findall/3 for a goal that passes its answers to a continuation: the list is the
%   program's own (the result of its findall/3 or aggregate_all/3).

dl_findall_k(G, L) :- dl_findall_k(G, L, []).
dl_findall_k(G, L, T) :-
    setup_call_cleanup('$new_findall_bag',
                       ( ( call(G) -> true ; true ), '$collect_findall_bag'(L, T) ),
                       '$destroy_findall_bag').

%!  dl_aggregate_k(+Spec, +StreamGoal, -Result)
%   aggregate_all/3 (count, sum, max, min, bag, set) over the values collected.

dl_aggregate_k(F, G, R) :- dl_findall_k(G, Vs), dl_aggregate(F, Vs, R).

dl_aggregate(count, Vs, N) :- length(Vs, N).
dl_aggregate(sum, Vs, S) :- sum_list(Vs, S0), S is S0.
dl_aggregate(max, [V|Vs], M) :- foldl(dl_max, Vs, V, M0), M is M0.
dl_aggregate(min, [V|Vs], M) :- foldl(dl_min, Vs, V, M0), M is M0.
dl_aggregate(bag, Vs, Vs).
dl_aggregate(set, Vs, S) :- sort(Vs, S).

dl_max(X, A, M) :- ( X > A -> M = X ; M = A ).
dl_min(X, A, M) :- ( X < A -> M = X ; M = A ).

%!  dl_gen_k(+Generator, +K)
%   Pass each answer of a builtin generator to K, made one at a time and never stored.
%   member/2, between/3, select/3, nth0/3, nth1/3 and append/3 (splitting a list) are
%   enumerated here; any other builtin is run by Prolog inside the commit, so its choicepoints
%   are gone when the call returns.

dl_gen_k(M:G, K) :- dl_gen(G, M, K).

dl_gen(member(X, L), _, K) :- is_list(L), !, dl_member_k(L, X, K).
dl_gen(between(L, H, X), _, K) :-
    integer(L), ( integer(H) ; H == inf ; H == infinite ), var(X), !,
    dl_between_k(L, H, X, K).
dl_gen(select(X, L, R), _, K) :- is_list(L), !, dl_select_k(L, X, R, K).
dl_gen(nth0(I, L, E), _, K) :- var(I), is_list(L), !, dl_nth_k(L, 0, I, E, K).
dl_gen(nth1(I, L, E), _, K) :- var(I), is_list(L), !, dl_nth_k(L, 1, I, E, K).
dl_gen(append(X, Y, L), _, K) :- var(X), is_list(L), !, dl_append_k(L, X, Y, K).
dl_gen(G, M, K) :- ( call(M:G), dl_k(K) -> true ; fail ).

dl_member_k([Y|Ys], X, K) :-
    (   Ys == []
    ->  X = Y, dl_k(K)
    ;   ( X = Y, dl_k(K) -> true ; dl_member_k(Ys, X, K) )
    ).

dl_between_k(I, H, X, K) :-
    I =< H,
    (   X = I, dl_k(K) -> true
    ;   I1 is I + 1, dl_between_k(I1, H, X, K)
    ).

dl_select_k([H|T], X, R, K) :-
    (   X = H, R = T, dl_k(K) -> true
    ;   R = [H|R1], dl_select_k(T, X, R1, K)
    ).

dl_nth_k([X|Xs], I0, I, E, K) :-
    (   I = I0, E = X, dl_k(K) -> true
    ;   I1 is I0 + 1, dl_nth_k(Xs, I1, I, E, K)
    ).

dl_append_k(L, X, Y, K) :-
    (   X = [], Y = L, dl_k(K) -> true
    ;   L = [H|T], X = [H|X1], dl_append_k(T, X1, Y, K)
    ).

%!  dl_match_k(+Facts, +Call, +K)
%   Facts written as data: each fact that unifies with Call, in order, passed to K.

dl_match_k([F|Fs], C, K) :-
    (   ( ground(F) -> F1 = F ; copy_term(F, F1) ), C = F1, dl_k(K) -> true
    ;   dl_match_k(Fs, C, K)
    ).

%!  dl_solve_between(+Lo, +Hi, +Expr, -X)
%   between(Lo, Hi, X), X =:= Expr, for Expr free of X: at most one answer, the integer
%   value of Expr when it lies in Lo..Hi.

dl_solve_between(Lo, Hi, E, X) :-
    (   integer(Lo), ( integer(Hi) ; Hi == inf ; Hi == infinite )
    ->  X0 is E, X is truncate(X0), X =:= X0, Lo =< X, X =< Hi
    ;   between(Lo, Hi, X), X =:= E                      % raises between/3's error
    ).

%!  dl_once(+Goal)
%   The first answer of a builtin goal (once/1 for builtins).

dl_once(G) :- ( call(G) -> true ; fail ).

%!  dl_member(?X, +Answers)
%   Where ordinary Prolog calls a converted nondeterministic predicate by name, its answers
%   are given back one by one, as member/2 does.

dl_member(X, [Y|Ys]) :- dl_member_(Ys, X, Y).
dl_member_(_, X, X).
dl_member_([Y|Ys], X, _) :- dl_member_(Ys, X, Y).
