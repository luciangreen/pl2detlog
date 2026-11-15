/*  detlog_runtime.pl - the Detlog runtime for SWI-Prolog, written by pl2detlog.

    Load it before a converted program:   ?- [detlog_runtime], [program_detlog].
    Run a query predicate:                 ?- '$query1__cp'(X, Rows).

    The library is written in the style it supports: no cut, no ;, no ->, no \+, no findall/3,
    and clauses are told apart by their first argument, so first-argument indexing leaves no
    choicepoint.  if_commit/3 is the one primitive commitment construct: it takes the first
    answer of its condition (conditions are deterministic builtins), and runs the else branch
    only when the condition has no answer.
*/

:- dynamic('$detlog_memo'/2).

if_commit(C, T, E) :- ( call(C) -> call(T) ; call(E) ).

% ---- packets: lists of e(Row), out(Text) and cut items ----
rows_concat([], []).
rows_concat([L|Ls], R) :- rows_concat(Ls, R0), dl_append(L, R0, R).

dl_append([], L, L).
dl_append([X|Xs], L, [X|R]) :- dl_append(Xs, L, R).

% cut markers: stop after the first list that contains one
rows_concat_cut([], []).
rows_concat_cut([L|Ls], R) :- if_commit(dl_has_cut(L), R = L, (rows_concat_cut(Ls, R0), dl_append(L, R0, R))).
rows_cut_concat(Ls, R) :- rows_concat_cut(Ls, R0), strip_cut(R0, R).
strip_cut([], []).
strip_cut([I|Is], R) :- dl_strip(I, Is, R).
dl_strip(cut, Is, R) :- strip_cut(Is, R).
dl_strip(e(X), Is, [e(X)|R]) :- strip_cut(Is, R).
dl_strip(out(T), Is, [out(T)|R]) :- strip_cut(Is, R).
dl_has_cut([I|Is]) :- if_commit(I == cut, true, dl_has_cut(Is)).
cut_in(e(_), O) :- dl_has_cut(O).

% splice_extend(Packet, Pattern, e(Env), Out): each answer row, unified with the call, extends Env
splice_extend([], _, _, []).
splice_extend([I|Is], Pat, Env, Out) :- dl_se(I, Pat, Env, O1), splice_extend(Is, Pat, Env, O2), dl_append(O1, O2, Out).
dl_se(out(T), _, _, [out(T)]).
dl_se(cut, _, _, [cut]).
dl_se(e(R), Pat, Env, O) :- copy_term(Pat-Env, P2-E2), if_commit(P2 = R, O = [E2], O = []).

% project_rows(EnvPacket, EnvVars, HeadArgs, Rows)
project_rows([], _, _, []).
project_rows([I|Is], Vs, H, Out) :- dl_pr(I, Vs, H, O1), project_rows(Is, Vs, H, O2), dl_append(O1, O2, Out).
dl_pr(out(T), _, _, [out(T)]).
dl_pr(cut, _, _, [cut]).
dl_pr(e(R), Vs, H, O) :- copy_term(Vs-H, V2-H2), if_commit(V2 = R, O = [e(H2)], O = []).

% project_list(Rows, e(EnvPattern), Template, Values)
project_list([], _, _, []).
project_list([I|Is], EP, T, Out) :- dl_pl(I, EP, T, O1), project_list(Is, EP, T, O2), dl_append(O1, O2, Out).
dl_pl(out(_), _, _, []).
dl_pl(cut, _, _, []).
dl_pl(e(R), EP, T, O) :- copy_term(EP-T, E2-T2), if_commit(E2 = e(R), O = [T2], O = []).

% packet_first(Packet, OutputBeforeFirstRow, [FirstRow] or [])
packet_first([], [], []).
packet_first([I|Is], Pre, F) :- dl_pf(I, Is, Pre, F).
dl_pf(out(T), Is, [out(T)|Pre], F) :- packet_first(Is, Pre, F).
dl_pf(cut, Is, Pre, F) :- packet_first(Is, Pre, F).
dl_pf(e(R), _, [], [e(R)]).

packet_split([], [], []).
packet_split([I|Is], O, R) :- dl_ps(I, Is, O, R).
dl_ps(out(T), Is, [out(T)|O], R) :- packet_split(Is, O, R).
dl_ps(cut, Is, O, R) :- packet_split(Is, O, R).
dl_ps(e(X), Is, O, [e(X)|R]) :- packet_split(Is, O, R).

% output as data
effect_text(G, T) :- with_output_to(string(T), G).

% facts: the rows that unify with the call
cp_filter([], _, []).
cp_filter([e(F)|Fs], Pat, Out) :- copy_term(Pat, P2), copy_term(F, F2), if_commit(P2 = F2, Out = [e(P2)|O], Out = O), cp_filter(Fs, Pat, O).

aggregate_list(S, Ts, R) :- dl_agg(S, Ts, R).
dl_agg(count, Ts, N) :- length(Ts, N).
dl_agg(sum, Ts, S) :- dl_sum(Ts, 0, S).
dl_agg(max, [T|Ts], M) :- X is T, dl_max(Ts, X, M).
dl_agg(min, [T|Ts], M) :- X is T, dl_min(Ts, X, M).
dl_agg(bag, Ts, Ts).
dl_agg(set, Ts, S) :- sort(Ts, S).
dl_sum([], S, S).
dl_sum([T|Ts], A, S) :- A1 is A + T, dl_sum(Ts, A1, S).
dl_max([], M, M).
dl_max([T|Ts], A, M) :- X is T, if_commit(X > A, dl_max(Ts, X, M), dl_max(Ts, A, M)).
dl_min([], M, M).
dl_min([T|Ts], A, M) :- X is T, if_commit(X < A, dl_min(Ts, X, M), dl_min(Ts, A, M)).

% independent generators: splice_safe/2 guard and the Cartesian product in Prolog order
splice_safe(A, B) :- term_variables(A, VA), term_variables(B, VB), dl_no_shared(VA, VB).
dl_no_shared([], _).
dl_no_shared([V|Vs], VB) :- if_commit(dl_var_in(VB, V), fail, dl_no_shared(Vs, VB)).
dl_var_in([W|Ws], V) :- if_commit(V == W, true, dl_var_in(Ws, V)).
splice2([], _, _, _, _, []).
splice2([A|As], PB, PatA, PatB, Env, Out) :- dl_sp(A, PB, PatA, PatB, Env, O1), splice2(As, PB, PatA, PatB, Env, O2), dl_append(O1, O2, Out).
dl_sp(out(T), _, _, _, _, [out(T)]).
dl_sp(e(RA), PB, PatA, PatB, Env, Out) :- dl_sp2(PB, RA, PatA, PatB, Env, Out).
dl_sp2([], _, _, _, _, []).
dl_sp2([B|Bs], RA, PatA, PatB, Env, Out) :- dl_sp3(B, RA, PatA, PatB, Env, O1), dl_sp2(Bs, RA, PatA, PatB, Env, O2), dl_append(O1, O2, Out).
dl_sp3(out(_), _, _, _, _, []).
dl_sp3(e(RB), RA, PatA, PatB, Env, O) :- copy_term(f(PatA, PatB, Env), f(A2, B2, E2)), if_commit((A2 = RA, B2 = RB), O = [E2], O = []).

% memo tables, keyed by call variant
memo_lookup(K, Args, Found) :-
    copy_term(K-Args, Key), numbervars(Key, 0, _),
    if_commit('$detlog_memo'(Key, Stored), (copy_term(Stored, f(A2, R2)), A2 = Args, Found = found(R2)), Found = none).
memo_store(K, Args, Rows) :-
    copy_term(K-Args, Key), numbervars(Key, 0, _),
    if_commit('$detlog_memo'(Key, _), true, assertz('$detlog_memo'(Key, f(Args, Rows)))).

% S2A loops: row I of s2a(K, Columns) for I = 0..K-1; a bound integer on a linear column is solved directly
s2a_rows(s2a(K, Cols), Args, Rows) :-
    if_commit(dl_s2a_direct(Cols, Args, K, Is), true, (K1 is K - 1, dl_numlist(0, K1, Is))),
    dl_s2a_loop(Is, Cols, Args, Rows).
dl_s2a_direct([C|Cs], [A|As], K, Is) :- if_commit(dl_s2a_solve(C, A, K, Is0), Is = Is0, dl_s2a_direct(Cs, As, K, Is)).
dl_s2a_solve(newton([D0, D1]), A, K, Is) :-
    integer(A), D1 =\= 0,
    if_commit((0 is (A - D0) mod D1, I is (A - D0) // D1, I >= 0, I < K), Is = [I], Is = []).
dl_numlist(L, H, Ls) :- if_commit(L > H, Ls = [], (Ls = [L|T], L1 is L + 1, dl_numlist(L1, H, T))).
dl_s2a_loop([], _, _, []).
dl_s2a_loop([I|Is], Cols, Args, Rows) :-
    dl_s2a_row(Cols, I, Row), copy_term(Args, A2),
    if_commit(A2 = Row, Rows = [e(A2)|R1], Rows = R1),
    dl_s2a_loop(Is, Cols, Args, R1).
dl_s2a_row([], _, []).
dl_s2a_row([C|Cs], I, [V|Vs]) :- dl_s2a_val(C, I, V), dl_s2a_row(Cs, I, Vs).
dl_s2a_val(const(T), _, T).
dl_s2a_val(data(Vs), I, V) :- nth0(I, Vs, V).
dl_s2a_val(newton(Ds), I, V) :- dl_newton(Ds, I, 0, 1, 0, V).
% sum of D_k * C(I, k); C(I, k+1) = C(I, k) * (I - k) / (k + 1)
dl_newton([], _, _, _, V, V).
dl_newton([D|Ds], I, K, C, A, V) :- A1 is A + D * C, C1 is C * (I - K) // (K + 1), K1 is K + 1, dl_newton(Ds, I, K1, C1, A1, V).

% nondeterministic builtins as packets: candidate instances of the goal, in Prolog order.
% splice_extend/4 keeps the candidates that unify with the call.
builtin_rows(G, P) :- functor(G, F, N), if_commit(dl_br_known(F, N), dl_br(F, G, P), dl_br_other(G, P)).
dl_br_known(member, 2). dl_br_known(between, 3). dl_br_known(append, 3). dl_br_known(select, 3).
dl_br_known(nth0, 3). dl_br_known(nth1, 3). dl_br_known(length, 2). dl_br_known(last, 2).
dl_br(member, member(X, L), P) :- dl_member_rows(L, X, L, P).
dl_br(between, between(L, H, X), P) :- if_commit(integer(X), if_commit((X >= L, X =< H), P = [e([between(L, H, X)])], P = []), (H \== inf, H \== infinite, dl_between_rows(L, H, L, P))).
dl_br(append, append(A, B, C), P) :- if_commit(is_list(A), (dl_append(A, B, C2), P = [e([append(A, B, C2)])]), dl_append_rows(C, [], C, A, B, P)).
dl_br(select, select(X, L, R), P) :- dl_select_rows(L, [], X, L, R, P).
dl_br(nth0, nth0(I, L, E), P) :- dl_nth_rows(L, 0, nth0, I, L, E, P).
dl_br(nth1, nth1(I, L, E), P) :- dl_nth_rows(L, 1, nth1, I, L, E, P).
dl_br(length, length(L, N), P) :- length(L, N), P = [e([length(L, N)])].
dl_br(last, last(L, X), P) :- if_commit(last(L, X0), P = [e([last(L, X0)])], P = []).
dl_member_rows([], _, _, []).
dl_member_rows([H|T], X, L, [e([member(H, L)])|P]) :- dl_member_rows(T, X, L, P).
dl_between_rows(I, H, L0, P) :- if_commit(I > H, P = [], (P = [e([between(L0, H, I)])|P1], I1 is I + 1, dl_between_rows(I1, H, L0, P1))).
dl_append_rows([], Pre, C, _, _, [e([append(PreR, [], C)])]) :- reverse(Pre, PreR).
dl_append_rows([X|Xs], Pre, C, A, B, [e([append(PreR, [X|Xs], C)])|P]) :- reverse(Pre, PreR), dl_append_rows(Xs, [X|Pre], C, A, B, P).
dl_select_rows([], _, _, _, _, []).
dl_select_rows([X|Xs], Pre, X0, L, R0, [e([select(X, L, R)])|P]) :- reverse(Pre, PreR), dl_append(PreR, Xs, R), dl_select_rows(Xs, [X|Pre], X0, L, R0, P).
dl_nth_rows([], _, _, _, _, _, []).
dl_nth_rows([X|Xs], K, F, I, L, E, [e([G])|P]) :- G =.. [F, K, L, X], K1 is K + 1, dl_nth_rows(Xs, K1, F, I, L, E, P).
% other nondeterministic builtins (sub_atom/5, permutation/2, ...) have no deterministic enumerator here
dl_br_other(G, P) :- findall(e([G]), G, P).

detlog_unsupported(PI, Msg) :- throw(error(detlog_unsupported(PI, Msg), _)).

% print a query packet the way the pl2detlog app does
detlog_print(Names, Rows) :- dl_print(Rows, Names).
dl_print([], _).
dl_print([I|Is], Ns) :- dl_print_item(I, Ns), dl_print(Is, Ns).
dl_print_item(out(T), _) :- write(T).
dl_print_item(cut, _).
dl_print_item(e(Vs), Ns) :- if_commit(Ns = [], writeln(true), (dl_print_vals(Ns, Vs), nl)).
dl_print_vals([N|Ns], [V|Vs]) :- format("~w = ~q", [N, V]), dl_print_more(Ns, Vs).
dl_print_more([], []).
dl_print_more([N|Ns], [V|Vs]) :- format(", ~w = ~q", [N, V]), dl_print_more(Ns, Vs).
