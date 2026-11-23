/*  detlog_rt.pl -- the Detlog runtime for code written by pl2detlog.pl

    Converted files load it with  :- use_module(library(detlog_rt)).
    (or with a relative path when the module is not installed as a pack).

    Detlog code has no cut, no ;, no ->, no \+, no findall/3 and no call/N.
    if_commit/3 is its one decision construct: it takes the first answer of a
    deterministic condition and runs Then, or runs Else when the condition has
    no answer.  When this library is loaded, if_commit/3 is compiled inline as
    (C -> T ; E), so it costs nothing at run time.

    Answer lists.  A nondeterministic predicate p/N is written as
    p__all(A1, ..., AN, Answers, Tail): Answers-Tail is a difference list of
    the instances p(A1', ..., AN') that Prolog would give for the call, in
    Prolog's order.  The helpers below make and read such lists.
*/

:- module(detlog_rt,
          [ if_commit/3,
            dl_all/3,          % +Goal, -Answers, ?Tail: answers of a builtin generator
            dl_once/1,         % +Goal: first answer of a builtin generator
            dl_match/4,        % +Facts, +Call, -Answers, ?Tail: facts as data
            dl_project/4,      % +Answers, +Pattern, +Template, -Values
            dl_aggregate/3,    % +Spec, +Values, -Result
            dl_member/2,       % ?X, +Answers: the boundary to backtracking Prolog
            dl_fused_first/2,  % +Generator, +Test: first answer, enumerated lazily
            dl_fused_all/5     % +Generator, +Test, +Answer, -Answers, ?Tail
          ]).

:- multifile user:goal_expansion/2.
:- dynamic user:goal_expansion/2.
user:goal_expansion(if_commit(C, T, E), (C -> T ; E)).

%!  if_commit(:Cond, :Then, :Else)
%   The Detlog decision: the first answer of Cond selects Then, no answer selects Else.

:- meta_predicate if_commit(0, 0, 0), dl_all(0, -, ?), dl_once(0),
                  dl_fused_first(0, 0), dl_fused_all(0, 0, ?, -, ?).

if_commit(C, T, E) :- ( call(C) -> call(T) ; call(E) ).

%!  dl_all(+Goal, -Answers, ?Tail)
%   Answers-Tail lists the instances of Goal, in Prolog's order.  The common
%   generators are enumerated directly; any other goal is collected.

dl_all(_:G, _, _) :- dl_infinite(G), !,
    throw(error(detlog_infinite_answers(G), context(dl_all/3, 'a list of all its answers would be infinite'))).
dl_all(M:G, As, T) :- dl_gen(G, As, T), !, M = M.
dl_all(M:G, As, T) :- findall(G, M:G, As, T).

dl_infinite(between(_, H, X)) :- var(X), ( H == inf ; H == infinite ).
dl_infinite(repeat).

dl_gen(member(X, L), As, T) :- nonvar(L), dl_member_all(L, X, L, As, T).
dl_gen(between(L, H, X), As, T) :- integer(L), integer(H), var(X), dl_between_all(L, H, L, As, T).
dl_gen(nth0(I, L, E), As, T) :- var(I), is_list(L), dl_nth_all(L, 0, nth0, L, E, As, T).
dl_gen(nth1(I, L, E), As, T) :- var(I), is_list(L), dl_nth_all(L, 1, nth1, L, E, As, T).

dl_member_all([], _, _, T, T).
dl_member_all([Y|Ys], X, L, As, T) :-
    (   \+ X \= Y
    ->  As = [member(Y, L)|As1]
    ;   As = As1
    ),
    (   nonvar(Ys) -> dl_member_all(Ys, X, L, As1, T)
    ;   findall(member(X, L), member(X, Ys), As1, T)
    ).

dl_between_all(I, H, L, As, T) :-
    (   I > H
    ->  As = T
    ;   As = [between(L, H, I)|As1],
        I1 is I + 1,
        dl_between_all(I1, H, L, As1, T)
    ).

dl_nth_all([], _, _, _, _, T, T).
dl_nth_all([X|Xs], K, F, L, E, As, T) :-
    G =.. [F, K, L, X],
    (   \+ E \= X -> As = [G|As1] ; As = As1 ),
    K1 is K + 1,
    dl_nth_all(Xs, K1, F, L, E, As1, T).

%!  dl_once(+Goal)
%   The first answer of a builtin goal (once/1 for builtins).

dl_once(G) :- ( call(G) -> true ; fail ).

%!  dl_match(+Facts, +Call, -Answers, ?Tail)
%   Facts written as data: the facts that unify with Call, in order.

dl_match([], _, T, T).
dl_match([F|Fs], C, As, T) :-
    (   \+ C \= F
    ->  copy_term(F, F1), As = [F1|As1]
    ;   As = As1
    ),
    dl_match(Fs, C, As1, T).

%!  dl_project(+Answers, +Pattern, +Template, -Values)
%   findall/3 over an answer list: Template for each answer that unifies with Pattern.

dl_project([], _, _, []).
dl_project([A|As], P, T, Vs) :-
    copy_term(P-T, P1-T1),
    (   P1 = A -> Vs = [T1|Vs1] ; Vs = Vs1 ),
    dl_project(As, P, T, Vs1).

%!  dl_aggregate(+Spec, +Values, -Result)
%   aggregate_all/3 over the values of an answer list.

dl_aggregate(count, Vs, N) :- length(Vs, N).
dl_aggregate(sum, Vs, S) :- sum_list(Vs, S0), S is S0.
dl_aggregate(max, [V|Vs], M) :- foldl(dl_max, Vs, V, M0), M is M0.
dl_aggregate(min, [V|Vs], M) :- foldl(dl_min, Vs, V, M0), M is M0.
dl_aggregate(bag, Vs, Vs).
dl_aggregate(set, Vs, S) :- sort(Vs, S).

dl_max(X, A, M) :- ( X > A -> M = X ; M = A ).
dl_min(X, A, M) :- ( X < A -> M = X ; M = A ).

%!  dl_member(?X, +Answers)
%   Where Detlog code meets ordinary Prolog (a meta-call, or a predicate kept
%   as Prolog), the answers are given back one by one, as member/2 does.

dl_member(X, [Y|Ys]) :- dl_member_(Ys, X, Y).
dl_member_(_, X, X).
dl_member_([Y|Ys], X, _) :- dl_member_(Ys, X, Y).

%!  dl_fused_first(+Generator, +Test)
%!  dl_fused_all(+Generator, +Test, +Answer, -Answers, ?Tail)
%   MNN fusion: a builtin generator whose answers are filtered by deterministic Test is
%   one loop.  The generator's answers are made one at a time and never stored; the first
%   that passes Test is kept (dl_fused_first/2), or each that passes adds Answer
%   (dl_fused_all/5).  No choicepoint is left when the call returns.

dl_fused_first(G, Test) :- ( call(G), call(Test) -> true ; fail ).

dl_fused_all(G, Test, Ans, As, T) :- findall(Ans, ( call(G), call(Test) ), As, T).
