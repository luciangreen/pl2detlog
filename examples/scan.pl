% First-match scans (rules ite_scan and neg_scan).
% A committed condition (member(X, Xs), Filters) becomes one recursive scan
% that stops at the first element passing the filters, as Prolog does:
% later elements are never tested, so they cannot raise errors.

% A cut local to findall's goal.
firsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).

% once/1, and an if-then-else with a real then-branch.
first_big(L, X) :- once((member(X, L), X > 10)).
label(L, R) :- ( member(X, L), X mod 2 =:= 0 -> R = even(X) ; R = none ).

% \+ is the same scan with T = fail and F = true.
all_small(L) :- \+ (member(X, L), X >= 10).

% The element can be a pattern; a deterministic prefix runs once.
key_of(K, Pairs, V) :- once(member(K-V, Pairs)).
above(N, L, Y) :- ( M is N * 2, member(Y, L), Y > M -> true ; Y = none ).
