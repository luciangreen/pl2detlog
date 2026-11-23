:- module(report, [report/1, total/2]).
% writing a report of Item-Value pairs

report(Pairs) :-
    forall(member(I-V, Pairs), line(I, V)),
    total(Pairs, T),
    format("total: ~w~n", [T]).

line(I, V) :- V > 0, !, format("~w: ~w~n", [I, V]).
line(I, _) :- format("~w: none~n", [I]).

total([], 0).
total([_-V|Ps], T) :- total(Ps, T0), T is T0 + V.
