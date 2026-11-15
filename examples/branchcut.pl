% The cut in the then-branch cuts the whole clause: member/2's later
% answers and pick/2's second clause.  Detlog writes it as a cut marker:
% the row loop stops after it and the later clause is dropped.
pick(N, X) :- ( N > 3 -> member(X, [big, huge]), ! ; X = small ).
pick(_, other).

first_over(L, Min, X) :- member(X, L), ( X > Min -> ! ; fail ).
first_over(_, _, none).

w(X) :- member(X, [1, 2, 3]), write(X), ( X >= 2 -> nl, ! ; true ).
w(last).
