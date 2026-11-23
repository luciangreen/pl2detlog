/*  detlog_stream_rt.pl - the stream code's runtime for SWI-Prolog (src/stream.js), written by pl2detlog.

    Load it with detlog_runtime.pl before a converted program in the stream form (the default):
        ?- [detlog_runtime, detlog_stream_rt], [program_detlog].
        ?- '$query1__cp'(X, Rows), detlog_print(['X'], Rows).

    Bags collect answers (findall/3, aggregate_all/3 and the query boundary) and cut cells record a cut
    inside ; or ->.  Both are terms changed in place (nb_linkarg/3, nb_setarg/3), so backtracking does
    not undo them.  At the query boundary the program's output goes to a temporary file, and the text
    written before each answer becomes an out(Text) item before its e(Row): the query packet is the one
    packet code builds.  (The app's own engines and the C export implement the same predicates natively.)
*/

% a bag: '$bag'(ItemsReversed)
dl_bag_new('$bag'([])).
dl_bag_add(B, T) :- duplicate_term(T, C), arg(1, B, L), nb_linkarg(1, B, [C|L]).
dl_bag_list(B, L) :- arg(1, B, R), reverse(R, L).
dl_bag_list(B, L, Tail) :- arg(1, B, R), dl_rev_onto(R, Tail, L).
dl_bag_count(B, C) :- arg(1, B, R), dl_count_e(R, 0, C).
dl_count_e([], C, C).
dl_count_e([X|Xs], A, C) :- if_commit(X = e(_), A1 is A + 1, A1 = A), dl_count_e(Xs, A1, C).
dl_rev_onto([], L, L).
dl_rev_onto([X|Xs], A, L) :- dl_rev_onto(Xs, [X|A], L).

% the query boundary: '$qbag'(ItemsReversed, File, Stream, OldOutput); pos(N) marks the text written so far
dl_query_new('$qbag'([], F, S, Old)) :-
    tmp_file_stream(text, F, S), current_output(Old), set_output(S).
dl_bag_row(B, Vs) :- duplicate_term(Vs, C), dl_qmark(B), dl_qpush(B, e(C)).
dl_bag_rows(B, R) :- dl_qmark(B), dl_qfinish(B, R).
dl_bag_last(B, Vs, R) :- dl_qmark(B), dl_qpush(B, e(Vs)), dl_qfinish(B, R).
dl_qmark(B) :- arg(3, B, S), flush_output(S), character_count(S, N), dl_qpush(B, pos(N)).
dl_qpush(B, X) :- arg(1, B, L), nb_linkarg(1, B, [X|L]).
dl_qfinish(B, R) :-
    B = '$qbag'(Rev, F, S, Old),
    set_output(Old), close(S), read_file_to_string(F, Text, []), delete_file(F),
    reverse(Rev, Items), dl_qitems(Items, Text, 0, R).
dl_qitems([], _, _, []).
dl_qitems([I|Is], T, P, R) :- dl_qitem(I, Is, T, P, R).
dl_qitem(pos(N), Is, T, P, R) :-
    if_commit(N > P, (L is N - P, sub_string(T, P, L, _, S), R = [out(S)|R1]), R = R1),
    dl_qitems(Is, T, N, R1).
dl_qitem(e(Vs), Is, T, P, [e(Vs)|R]) :- dl_qitems(Is, T, P, R).

% first-argument dispatch: X is bound and has P's principal functor
dl_has_key(X, P) :- nonvar(X), functor(X, N, A), functor(P, N, A).

% a cut cell: '$cut'(false) until the cut runs
dl_cut_new('$cut'(false)).
dl_cut_set(C) :- nb_setarg(1, C, true).
dl_cut_off(C) :- arg(1, C, false).
