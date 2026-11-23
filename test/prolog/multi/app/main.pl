% A program in three folders: app/ includes facts from lib/ and uses a module
% from lib/text/.  The converted program keeps the same folders, so every
% relative path in an include or use_module still finds its file.
:- include('../lib/inventory.pl').
:- use_module('../lib/text/report').

:- initialization(main, main).

main :-
    findall(Item-Total, stock_value(Item, Total), Pairs),
    report(Pairs),
    cheapest(Item),
    format("cheapest: ~w~n", [Item]).

stock_value(Item, Total) :-
    stock(Item, Count),
    price(Item, Price),
    Total is Count * Price.

cheapest(Item) :-
    findall(P-I, price(I, P), Ps),
    msort(Ps, [_-Item|_]).
