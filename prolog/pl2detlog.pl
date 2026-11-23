/*  pl2detlog.pl -- Prolog to Detlog and Detlog MNN, in SWI-Prolog

    ?- use_module(library(pl2detlog)).
    ?- pl2detlog_convert('prog.pl', []).                 % writes prog_detlog/ and prog_mnn/
    ?- pl2detlog_compile('prog.pl', [main(main)]).       % builds ./prog, in the fastest form

    Command line (see README.md):
       swipl pl2detlog convert prog.pl [-g main | -q "Query"] [--form mnn] [--out Dir]
       swipl pl2detlog compile prog.pl [-g main | -q "Query"] [-o exe]

    The three forms
      prolog  the program as written;
      detlog  Detlog: no cut, ;, ->, \+, findall/3 or call/N in the program.  A predicate whose
              clauses are told apart by a bound argument stays a plain predicate (it leaves no
              choicepoint); a nondeterministic one becomes p__all/N+2, which returns its
              answers as a list; a necessary cut becomes if_commit/3; an unnecessary cut is
              dropped;
      mnn     Detlog MNN: Detlog plus the MNN rewrites -- clauses told apart by guard tests,
              first-answer versions p__first/N, tabling of pure tree recursion (MEMO), the
              accumulator rewrite of append-recursion, facts as data.

    Proofs are kept out of the code: each rewrite's side conditions are checked here and
    listed in PROOFS.txt in the output folder, and the compile step checks that every form
    gives Prolog's output on the query before it times them.
*/

:- module(pl2detlog,
          [ pl2detlog_convert/2,      % +File, +Options
            pl2detlog_convert/3,      % +File, +Form, +Options
            pl2detlog_compile/2,      % +File, +Options
            pl2detlog_check/3,        % +File, +Options, -Results
            pl2detlog_cli/1           % +Argv
          ]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(option)).
:- use_module(library(readutil)).
:- use_module(library(dcg/basics), []).

:- dynamic
    src_file/2,          % Seq, Path
    dbv/5,               % Kind, Key, Term, Vars, Hints
    pred_key/2,          % Key, Seq
    dyn_key/1,
    export_key/1,
    aux_of/2,            % Aux, Parent
    aux_root/2,          % Aux, RootKey
    kept/2,              % Key, Reason
    m_pat/2,
    m_succ/2,
    det_key/1,
    eff_key/1,
    inf_key/1,
    callable_key/1,
    has_caller/1,
    need/2,
    done/2,
    table_key/1,
    inlined/1,
    note/2,
    form/1,
    counter/2,
    entry/2,             % Name, Goal       (the query/main entry)
    root_dir/1.

:- meta_predicate safe_test(0).

%  Variable names travel with the terms as attributes.
attr_unify_hook(_, _).
attribute_goals(_) --> [].

:- create_prolog_flag(pl2detlog_verbose, false, [keep(true)]).

                 /*******************************
                 *          PUBLIC API          *
                 *******************************/

%!  pl2detlog_convert(+File, +Options)
%   Write the Detlog and the Detlog MNN form of File (and every file it loads with a
%   relative path) into two folders next to its folder.  Options: form(detlog|mnn|both),
%   out(Dir) (the folder for a single form), main(Name) or query(Goal) (the entry: its
%   modes make more of the program deterministic).

pl2detlog_convert(File, Options) :-
    option(form(F), Options, both),
    (   F == both
    ->  pl2detlog_convert(File, detlog, Options),
        pl2detlog_convert(File, mnn, Options)
    ;   pl2detlog_convert(File, F, Options)
    ).

pl2detlog_convert(File, Form, Options) :-
    must_be(oneof([detlog, mnn]), Form),
    load_program(File),
    ( entry_from_options(Options, _) -> true ; true ),
    convert_form(Form),
    out_root(Form, Options, OutRoot),
    write_program(Form, OutRoot),
    root_out_file(OutRoot, Main),
    (   option(quiet(true), Options) -> true ; format(user_error, "% ~w: ~w~n", [Form, Main]) ).

%!  pl2detlog_compile(+File, +Options)
%   Convert File, run the query in each form (Prolog, Detlog, Detlog MNN), check each gives
%   Prolog's output, and build an executable of the fastest.  Options: main(Name) or
%   query(Goal) (needed when the program has no main/0 or initialization(main, main)),
%   exe(Path), forms(List), budget(Seconds).

pl2detlog_compile(File, Options) :-
    pl2detlog_check(File, Options, Results),
    report_results(Results, Best),
    absolute_file_name(File, Abs, [file_type(prolog), access(read)]),
    (   option(exe(Exe0), Options) -> true ; file_name_extension(Exe0, _, Abs) ),
    absolute_file_name(Exe0, Exe),
    Best = r(BForm, BDir, BMain, _, _),
    build_exe(BForm, BDir, BMain, Exe),
    format(user_error, "% built ~w (~w form)~n", [Exe, BForm]).

%!  pl2detlog_check(+File, +Options, -Results)
%   Convert File to each form and run the query in each, in a fresh process.  Results are
%   r(Form, Folder, MainFile, Answer-Output, SecondsPerRun).

pl2detlog_check(File, Options, Results) :-
    absolute_file_name(File, Abs, [file_type(prolog), access(read)]),
    load_program(Abs),
    (   entry_from_options([purpose(compile)|Options], Goal)
    ->  true
    ;   throw(error(pl2detlog(no_main), _))
    ),
    option(forms(Forms), Options, [prolog, detlog, mnn]),
    option(budget(Budget), Options, 0.5),
    (   option(quiet(true), Options) -> true ; format(user_error, "% query: ~q~n", [Goal]) ),
    Opts2 = [query(Goal)|Options],
    findall(Form-Dir-Main, form_files(Form, Forms, Abs, Opts2, Dir, Main), FDs),
    maplist(bench_form(Goal, Budget), FDs, Results).

form_files(prolog, Forms, Abs, _, Dir, Abs) :-
    memberchk(prolog, Forms),
    file_directory_name(Abs, Dir).
form_files(Form, Forms, Abs, Options, Dir, Main) :-
    member(Form, [detlog, mnn]),
    memberchk(Form, Forms),
    load_program(Abs),
    entry_from_options(Options, _),
    convert_form(Form),
    out_root(Form, Options, Dir),
    write_program(Form, Dir),
    root_out_file(Dir, Main).

                 /*******************************
                 *            LOADING           *
                 *******************************/

reset_all :-
    forall(member(P, [src_file/2, dbv/5, pred_key/2, dyn_key/1, export_key/1, entry/2,
                      root_dir/1]),
           ( P = N/A, functor(H, N, A), retractall(H) )),
    reset_form,
    (   current_module(pl2detlog_read) -> true ; true ).

reset_form :-
    forall(member(P, [aux_of/2, aux_root/2, kept/2, m_pat/2, m_succ/2, det_key/1, eff_key/1,
                      inf_key/1,
                      callable_key/1, has_caller/1, need/2, done/2, table_key/1, inlined/1,
                      note/2, form/1, counter/2]),
           ( P = N/A, functor(H, N, A), retractall(H) )),
    forall(member(K, [ncl, out, inl]), retractall(dbv(K, _, _, _, _))),
    forall(( pred_key(K, _), aux_name(K) ), retractall(pred_key(K, _))).

aux_name(N/_) :- sub_atom(N, _, _, _, '__').

load_program(File) :-
    reset_all,
    absolute_file_name(File, Abs, [file_type(prolog), access(read)]),
    load_file(Abs),
    findall(D, ( src_file(_, P), file_directory_name(P, D) ), Ds),
    common_dir(Ds, Root),
    assertz(root_dir(Root)).

load_file(Path) :- src_file(_, Path), !.
load_file(Path) :-
    aggregate_all(count, src_file(_, _), N),
    assertz(src_file(N, Path)),
    file_directory_name(Path, Dir),
    setup_call_cleanup(open(Path, read, S),
                       read_items(S, Path, Dir, 0),
                       close(S)).

read_items(S, Path, Dir, Seq) :-
    read_term(S, T, [ module(pl2detlog_read), variable_names(Vs), comments(Cs) ]),
    comment_texts(Cs, Txt),
    (   T == end_of_file
    ->  db_put(item, Path, it(Seq, eof, Txt))
    ;   names_attach(Vs),
        term_item(T, Dir, Item),
        db_put(item, Path, it(Seq, Item, Txt)),
        Seq1 is Seq + 1,
        read_items(S, Path, Dir, Seq1)
    ).

comment_texts(Cs, Txt) :-
    (   is_list(Cs) -> findall(C, member(_-C, Cs), Txt) ; Txt = [] ).

term_item((:- D), Dir, dir(D, Loads)) :- !,
    catch(dir_effects(D, Dir, Loads), _, Loads = []).
term_item((H --> B), _, Item) :- !,
    dcg_translate_rule((H --> B), Cl),
    cl_item(Cl, Item).
term_item(T, _, Item) :-
    cl_item(T, Item).

cl_item((H :- B), cl(H, B)) :- !, reg_head(H).
cl_item(H, cl(H, true)) :- reg_head(H).

reg_head(H) :-
    callable(H), H \= _:_, !,
    functor(H, N, A),
    (   pred_key(N/A, _) -> true
    ;   aggregate_all(count, pred_key(_, _), I), assertz(pred_key(N/A, I))
    ).
reg_head(_).

dir_effects(op(P, T, N), _, []) :- !, op(P, T, pl2detlog_read:N).
dir_effects(module(_, Ex), _, []) :- !,
    forall(member(op(P, T, N), Ex), op(P, T, pl2detlog_read:N)),
    forall(( member(K, Ex), K = _/_ ), assertz(export_key(K))).
dir_effects(dynamic(Spec), _, []) :- !,
    forall(spec_key(Spec, K), assertz(dyn_key(K))).
dir_effects(D, Dir, Loads) :-
    load_directive(D, Spec), !,
    local_loads(Spec, Dir, Loads).
dir_effects([H|T], Dir, Loads) :- !,
    local_loads([H|T], Dir, Loads).
dir_effects(_, _, []).

load_directive(include(F), F).
load_directive(consult(F), F).
load_directive(ensure_loaded(F), F).
load_directive(use_module(F), F).
load_directive(use_module(F, _), F).
load_directive(reexport(F), F).
load_directive(reexport(F, _), F).
load_directive(load_files(F, _), F).

spec_key(V, _) :- var(V), !, fail.
spec_key((A, B), K) :- !, ( spec_key(A, K) ; spec_key(B, K) ).
spec_key([H|T], K) :- !, member(S, [H|T]), spec_key(S, K).
spec_key(_:S, K) :- !, spec_key(S, K).
spec_key(N/A, N/A).
spec_key(as(S, _), K) :- spec_key(S, K).

local_loads(Fs, Dir, Loads) :- is_list(Fs), !,
    foldl(local_load(Dir), Fs, Loads, []).
local_loads(F, Dir, Loads) :-
    local_load(Dir, F, Loads, []).

local_load(Dir, F, [F-Abs|T], T) :-
    local_spec(F),
    absolute_file_name(F, Abs, [ file_type(prolog), access(read), relative_to(Dir),
                                 file_errors(fail) ]), !,
    load_file(Abs).
local_load(_, library(L), T, T) :- !,
    catch(pl2detlog_read:use_module(library(L)), _, true).
local_load(_, _, T, T).

local_spec(F) :- atom(F), !.
local_spec(F) :- string(F), !.
local_spec(A/B) :- local_spec(A), atomic(B).

common_dir([D], D) :- !.
common_dir([D|Ds], C) :-
    common_dir(Ds, C0),
    atomic_list_concat(P1, '/', D),
    atomic_list_concat(P2, '/', C0),
    common_prefix(P1, P2, P),
    atomic_list_concat(P, '/', C1),
    ( C1 == '' -> C = '/' ; C = C1 ).

common_prefix([X|Xs], [X|Ys], [X|Zs]) :- !, common_prefix(Xs, Ys, Zs).
common_prefix(_, _, []).

                 /*******************************
                 *   TERMS WITH VARIABLE NAMES  *
                 *******************************/

names_attach(Vs) :- maplist(name_pair, Vs).
name_pair(N=V) :- name_var(V, N).

name_var(V, N) :- var(V), \+ get_attr(V, pl2detlog, _), !, put_attr(V, pl2detlog, N).
name_var(_, _).

fresh(Hint, V) :- put_attr(V, pl2detlog, Hint).

var_hint(V, H) :- ( get_attr(V, pl2detlog, H0) -> H = H0 ; H = '' ).
set_hint(V, H) :- ( H \== '', var(V) -> put_attr(V, pl2detlog, H) ; true ).

db_put(Kind, Key, T) :-
    term_variables(T, Vs),
    maplist(var_hint, Vs, Hs),
    copy_term_nat(T-Vs, T2-Vs2),
    assertz(dbv(Kind, Key, T2, Vs2, Hs)).

db_get(Kind, Key, T) :-
    dbv(Kind, Key, T, Vs, Hs),
    maplist(set_hint, Vs, Hs).

db_all(Kind, Key, Ts) :-
    findall(T-Vs-Hs, dbv(Kind, Key, T, Vs, Hs), Raw),
    maplist(reattach, Raw, Ts).

reattach(T-Vs-Hs, T) :- maplist(set_hint, Vs, Hs).

                 /*******************************
                 *     THE PROGRAM, AS DATA     *
                 *******************************/

key(G, N/A) :- callable(G), functor(G, N, A).

src_clauses(K, Cls) :-
    findall((H :- B)-Vs-Hs,
            ( src_file(_, P),
              dbv(item, P, it(_, cl(H, B), _), Vs, Hs),
              key(H, K) ),
            Raw),
    maplist(reattach, Raw, Cls).

ncls(K, Cls) :- db_all(ncl, K, Cls).

user_goal(G) :-
    callable(G), G \= _:_,
    functor(G, N, A),
    ( pred_key(N/A, _) ; dyn_key(N/A) ), !.

conv_key(K) :- pred_key(K, _), \+ kept(K, _).

                 /*******************************
                 *         NORMALISATION        *
                 *******************************/

%   A normalised clause is cl(Head, plain(Goals)) or cl(Head, commit(Guard, Body)): the
%   clause had a cut; Guard is what came before it.  Goals are b(G) (builtin), u(G) (user
%   predicate), not(S), once(S), ignore(S), findall(T, S, L), findall4(T, S, L, T0) and
%   aggr(F, E, S, R), with S a b/1 or u/1 goal.  Inner control constructs become auxiliary
%   predicates (named Parent__ite1, Parent__or1, ...); maplist/foldl/include/exclude/
%   partition with a known closure become recursive predicates (Parent__map1, ...).

normalise :-
    forall(( pred_key(K, _), \+ aux_of(K, _) ), normalise_pred(K)).

normalise_pred(K) :-
    (   dyn_key(K)
    ->  assertz(kept(K, 'dynamic'))
    ;   src_clauses(K, Cls),
        catch(maplist(norm_clause(K), Cls),
              unsupported(Why),
              ( drop_aux(K), retractall(dbv(ncl, K, _, _, _)), assertz(kept(K, Why)) ))
    ).

drop_aux(K) :-
    forall(aux_of(A, K),
           ( drop_aux(A), retractall(aux_of(A, K)), retractall(aux_root(A, _)),
             retractall(pred_key(A, _)), retractall(dbv(ncl, A, _, _, _)) )).

norm_clause(K, (H :- B)) :-
    conj_list(B, Gs0),
    norm_goals(Gs0, [], K, H, Gs1),
    cut_kind(Gs1, K, H, Kind),
    db_put(ncl, K, cl(H, Kind)).

conj_list(V, [V]) :- var(V), !.
conj_list((A, B), L) :- !, conj_list(A, LA), conj_list(B, LB), append(LA, LB, L).
conj_list(true, []) :- !.
conj_list(G, [G]).

norm_goals([], _, _, _, []).
norm_goals([G|Gs], Before, K, H, Out) :-
    term_variables(H-Before-Gs, Outside),
    norm_goal(G, K, Outside, N),
    append(N, Rest, Out),
    norm_goals(Gs, [G|Before], K, H, Rest).

norm_goal(G, _, _, [b(call(G))]) :- var(G), !.
norm_goal(!, _, _, ['$cut']) :- !.
norm_goal(true, _, _, []) :- !.
norm_goal((A, B), K, O, N) :- !,
    conj_list((A, B), Gs),
    norm_goals(Gs, [], K, O, N).
norm_goal((C *-> _ ; _), _, _, _) :- nonvar(C), !, throw(unsupported('*->')).
norm_goal(D, K, O, [u(Aux)]) :- D = (_;_), !,
    disj_bodies(D, Bs),
    lift(K, or, O, D, Bs, Aux).
norm_goal((C -> T), K, O, [u(Aux)]) :- !,
    disj_bodies((C -> T), Bs),
    lift(K, ite, O, (C -> T), Bs, Aux).
norm_goal(\+ G, K, O, [not(S)]) :- !, simple(G, K, O, [], S).
norm_goal(not(G), K, O, [not(S)]) :- !, simple(G, K, O, [], S).
norm_goal(once(G), K, O, [once(S)]) :- !, simple(G, K, O, [], S).
norm_goal(ignore(G), K, O, [ignore(S)]) :- !, simple(G, K, O, [], S).
norm_goal(forall(C, A), K, O, N) :- !, norm_goal(\+ (C, \+ A), K, O, N).
norm_goal(findall(T, G, L), K, O, [findall(T, S, L)]) :- !, simple(G, K, O, T, S).
norm_goal(findall(T, G, L, T0), K, O, [findall4(T, S, L, T0)]) :- !, simple(G, K, O, T, S).
norm_goal(aggregate_all(Spec, G, R), K, O, [aggr(F, E, S, R)]) :-
    nonvar(Spec), aggr_spec(Spec, F, E), !,
    simple(G, K, O, E, S).
norm_goal(bagof(T, G0, L), K, O, [findall(T, S, L1), b(L1 \== []), b(L = L1)]) :-
    strip_hats(G0, G, QV), no_free(G, T, QV), !,
    fresh('L0', L1),
    simple(G, K, O, T, S).
norm_goal(setof(T, G0, L), K, O, [findall(T, S, L1), b(L1 \== []), b(sort(L1, L))]) :-
    strip_hats(G0, G, QV), no_free(G, T, QV), !,
    fresh('L0', L1),
    simple(G, K, O, T, S).
norm_goal(call(G), K, O, N) :- nonvar(G), !,
    (   contains_cut(G)
    ->  lift(K, call, O, G, [G], Aux), N = [u(Aux)]
    ;   norm_goal(G, K, O, N)
    ).
norm_goal(G, K, O, N) :-
    compound(G), G =.. [call, C|Extra], nonvar(C), !,
    closure_goal(C, Extra, K, O, G1),
    norm_goal(G1, K, O, N).
norm_goal(phrase(G, L), K, O, N) :- nonvar(G), !,
    norm_goal(phrase(G, L, []), K, O, N).
norm_goal(phrase(G, L, R), K, O, N) :- nonvar(G), !,
    dcg_translate_rule((pl2detlog_phrase --> G), (H :- B)),
    H =.. [_, L, R],
    conj_list(B, Gs),
    norm_goals(Gs, [], K, O, N).
norm_goal(G, K, O, [u(Aux)]) :-
    spec_meta(G, Kind, C, Lists, Extra), nonvar(C), closure_ok(C), !,
    spec_pred(K, O, Kind, C, Lists, Extra, Aux).
norm_goal(M:G, K, O, N) :- atom(M), callable(G), !,
    (   user_goal(G) -> norm_goal(G, K, O, N) ; N = [b(M:G)] ).
norm_goal(G, _, _, [u(G)]) :- user_goal(G), !.
norm_goal(G, _, _, [b(G)]).

disj_bodies((C -> T ; E), [(C1, !, T)|Bs]) :- !,
    local_cond(C, C1), no_tcut(T), disj_bodies(E, Bs).
disj_bodies((C -> T), [(C1, !, T)]) :- !, local_cond(C, C1), no_tcut(T).
disj_bodies((A ; B), [A|Bs]) :- !, no_tcut(A), disj_bodies(B, Bs).
disj_bodies(A, [A]) :- no_tcut(A).

local_cond(C, C1) :- ( contains_cut(C) -> C1 = call(C) ; C1 = C ).

no_tcut(G) :- ( contains_cut(G) -> throw(unsupported('cut inside ; or ->')) ; true ).

contains_cut(G) :- var(G), !, fail.
contains_cut(!).
contains_cut((A, B)) :- ( contains_cut(A) -> true ; contains_cut(B) ).
contains_cut((A ; B)) :- ( contains_cut(A) -> true ; contains_cut(B) ).
contains_cut((A -> B)) :- ( contains_cut(A) -> true ; contains_cut(B) ).
contains_cut((A *-> B)) :- ( contains_cut(A) -> true ; contains_cut(B) ).

strip_hats(G, G, []) :- var(G), !.
strip_hats(V^G0, G, [V|Vs]) :- !, strip_hats(G0, G, Vs).
strip_hats(G, G, []).

no_free(G, T, QV) :-
    term_variables(G, GV), term_variables(T-QV, TV),
    forall(member(V, GV), ( member(W, TV), W == V )).

aggr_spec(count, count, x).
aggr_spec(sum(E), sum, E).
aggr_spec(max(E), max, E).
aggr_spec(min(E), min, E).
aggr_spec(bag(E), bag, E).
aggr_spec(set(E), set, E).

%   simple(+G, +K, +Outside, +Template, -S): G as one b/u goal, lifting it when needed.
simple(G, K, O, T, S) :-
    term_variables(O-T, O2),
    (   simple_goal(G), norm_goal(G, K, O2, [S0]), ( S0 = b(_) ; S0 = u(_) )
    ->  S = S0
    ;   lift(K, sub, O2, G, [G], Aux),
        S = u(Aux)
    ).

simple_goal(G) :-
    callable(G), G \= _:_,
    functor(G, N, A),
    \+ memberchk(N/A, [ (',')/2, (;)/2, (->)/2, (*->)/2, (\+)/1, not/1, once/1, ignore/1,
                        forall/2, findall/3, findall/4, aggregate_all/3, bagof/3, setof/3,
                        phrase/2, phrase/3, call/1, (!)/0 ]).

%   lift(+Parent, +Kind, +Outside, +Construct, +Bodies, -AuxHead)
lift(K, Kind, O, Construct, Bodies, AuxHead) :-
    term_variables(Construct, CV),
    shared_vars(CV, O, Args),
    new_aux(K, Kind, Args, AuxHead),
    AuxHead =.. [_|_],
    key(AuxHead, AK),
    forall(member(B, Bodies),
           ( copy_term(AuxHead-B, H1-B1), norm_clause(AK, (H1 :- B1)) )).

shared_vars([], _, []).
shared_vars([V|Vs], O, S) :-
    (   member(W, O), W == V -> S = [V|S1] ; S = S1 ),
    shared_vars(Vs, O, S1).

new_aux(K, Kind, Args, Head) :-
    root_of(K, R),
    R = RN/_,
    next_count(R-Kind, N),
    format(atom(Name), '~w__~w~w', [RN, Kind, N]),
    length(Args, Ar),
    Head =.. [Name|Args],
    AK = Name/Ar,
    aggregate_all(count, pred_key(_, _), I),
    assertz(pred_key(AK, I)),
    assertz(aux_of(AK, K)),
    assertz(aux_root(AK, R)).

root_of(K, R) :- ( aux_root(K, R0) -> R = R0 ; R = K ).

next_count(Key, N) :-
    (   retract(counter(Key, N0)) -> N is N0 + 1 ; N = 1 ),
    assertz(counter(Key, N)).

%   once-cuts: G1, !, G2, !, G3  is  G1, !, once((G2, !)), G3
cut_kind(Gs, _, _, plain(Gs)) :- \+ memberchk('$cut', Gs), !.
cut_kind(Gs, K, H, commit(Guard, Body)) :-
    append(Guard, ['$cut'|Rest], Gs), \+ memberchk('$cut', Guard), !,
    (   memberchk('$cut', Rest)
    ->  last_cut(Rest, Pre, Post),
        term_variables(H-Guard-Post, O),
        term_variables(Pre, PV),
        shared_vars(PV, O, Args),
        new_aux(K, once, Args, Aux),
        key(Aux, AK),
        copy_term(Aux-Pre, A1-P1),
        cut_kind(P1, AK, A1, AKind),
        db_put(ncl, AK, cl(A1, AKind)),
        Body = [once(u(Aux))|Post]
    ;   Body = Rest
    ).

last_cut(Gs, Pre, Post) :-
    append(Pre0, ['$cut'|Post], Gs), \+ memberchk('$cut', Post), !,
    append(Pre0, ['$cut'], Pre).

%   closures
closure_ok(C) :- callable(C).

closure_goal(Ps>>B, Extra, K, O, G) :- !,
    lambda_closure(Ps>>B, Extra, K, O, C),
    add_args(C, Extra, G).
closure_goal(C, Extra, _, _, G) :- add_args(C, Extra, G).

add_args(M:C, Extra, M:G) :- !, add_args(C, Extra, G).
add_args(C, Extra, G) :- C =.. L0, append(L0, Extra, L), G =.. L.

lambda_closure(Lam, Extra, K, O, Closure) :-
    (   Lam = Free/(Ps>>B) -> true ; Lam = (Ps>>B), Free = [] ),
    is_list(Ps),
    length(Extra, NE), length(Ps, NP),
    (   NP =< NE -> true ; throw(unsupported('lambda with more parameters than arguments')) ),
    term_variables(B, BV), term_variables(Ps, PV), term_variables(Free-O, FO),
    exclude(var_in(PV), BV, NonParam),
    shared_vars(NonParam, FO, Shared),
    new_aux(K, lam, Shared, Closure),
    key(Closure, _),
    NR is NE - NP, length(Rest, NR),
    copy_term(Shared-Ps-B, Sh1-Ps1-B1),
    append(Ps1, Rest, Args),
    Closure =.. [Name|_],
    append(Sh1, Args, HA),
    H =.. [Name|HA],
    length(HA, Ar),
    retract(pred_key(Name/_, I)), assertz(pred_key(Name/Ar, I)),
    retract(aux_of(Name/AO, P)), assertz(aux_of(Name/Ar, P)), AO = AO,
    retract(aux_root(Name/_, R)), assertz(aux_root(Name/Ar, R)),
    (   Rest == [] -> B2 = B1 ; add_args(B1, Rest, B2) ),
    norm_clause(Name/Ar, (H :- B2)).

var_in(Vs, V) :- member(W, Vs), W == V, !.

spec_meta(maplist(C, A), map, C, [A], []).
spec_meta(maplist(C, A, B), map, C, [A, B], []).
spec_meta(maplist(C, A, B, D), map, C, [A, B, D], []).
spec_meta(maplist(C, A, B, D, E), map, C, [A, B, D, E], []).
spec_meta(foldl(C, A, V0, V), fold, C, [A], [V0, V]).
spec_meta(foldl(C, A, B, V0, V), fold, C, [A, B], [V0, V]).
spec_meta(foldl(C, A, B, D, V0, V), fold, C, [A, B, D], [V0, V]).
spec_meta(include(C, L, I), include, C, [L], [I]).
spec_meta(exclude(C, L, I), exclude, C, [L], [I]).
spec_meta(partition(C, L, I, E), partition, C, [L], [I, E]).

%   spec_pred(+Parent, +Outside, +Kind, +Closure, +Lists, +Extra, -Call)
spec_pred(K, O, Kind, C0, Lists, Extra, Call) :-
    length(Lists, NL),
    (   Kind == map -> NA = NL
    ;   Kind == fold -> NA is NL + 2
    ;   NA = 1
    ),
    length(CA, NA),
    (   ( C0 = _>>_ ; C0 = _/(_>>_) )
    ->  lambda_closure(C0, CA, K, O, C)
    ;   C = C0
    ),
    term_variables(C, CV),
    append(Lists, Extra, LE),
    append(LE, CV, Args),
    new_aux(K, Kind, Args, Call),
    key(Call, AK),
    Call =.. [Name|_],
    spec_clauses(Kind, Name, C, CV, NL, Cls),
    forall(member(Cl, Cls), ( Cl = (_ :- _) -> norm_clause(AK, Cl) ; norm_clause(AK, (Cl :- true)) )).

spec_clauses(map, Name, C, CV, NL, [H0, (H1 :- G, R)]) :-
    copy_term(C-CV, C1-CV1),
    length(Nils, NL), maplist(=([]), Nils),
    append(Nils, CV, A0), H0 =.. [Name|A0],
    length(Xs, NL), length(Ts, NL),
    maplist(hint('X'), Xs), maplist(hint('Xs'), Ts),
    maplist(cons, Xs, Ts, Cs),
    append(Cs, CV1, A1), H1 =.. [Name|A1],
    add_args(C1, Xs, G),
    append(Ts, CV1, AR), R =.. [Name|AR].
spec_clauses(fold, Name, C, CV, NL, [H0, (H1 :- G, R)]) :-
    copy_term(C-CV, C1-CV1),
    length(Nils, NL), maplist(=([]), Nils),
    fresh('V', V), append(Nils, [V, V|CV], A0), H0 =.. [Name|A0],
    length(Xs, NL), length(Ts, NL),
    maplist(hint('X'), Xs), maplist(hint('Xs'), Ts),
    maplist(cons, Xs, Ts, Cs),
    fresh('V0', V0), fresh('V1', V1), fresh('V', VV),
    append(Cs, [V0, VV|CV1], A1), H1 =.. [Name|A1],
    append(Xs, [V0, V1], GA), add_args(C1, GA, G),
    append(Ts, [V1, VV|CV1], AR), R =.. [Name|AR].
spec_clauses(Kind, Name, C, CV, 1, [H0, (H1 :- (G -> Yes ; No), R)]) :-
    memberchk(Kind, [include, exclude, partition]),
    copy_term(C-CV, C1-CV1),
    fresh('X', X), fresh('Xs', Xs),
    (   Kind == partition
    ->  A0 = [[], [], []|CV],
        fresh('I', I), fresh('I1', I1), fresh('E', E), fresh('E1', E1),
        A1 = [[X|Xs], I, E|CV1], RA = [Xs, I1, E1|CV1],
        Yes = (I = [X|I1], E = E1), No = (I = I1, E = [X|E1])
    ;   A0 = [[], []|CV],
        fresh('I', I), fresh('I1', I1),
        A1 = [[X|Xs], I|CV1], RA = [Xs, I1|CV1],
        (   Kind == include
        ->  Yes = (I = [X|I1]), No = (I = I1)
        ;   Yes = (I = I1), No = (I = [X|I1])
        )
    ),
    H0 =.. [Name|A0], H1 =.. [Name|A1], R =.. [Name|RA],
    add_args(C1, [X], G).

hint(H, V) :- fresh(H, V).
cons(X, T, [X|T]).

                 /*******************************
                 *     BUILTINS: WHAT THEY DO   *
                 *******************************/

%   Abstract values: a variable bound to '$g' stands for a ground term.

bind_g(T) :- term_variables(T, Vs), maplist(=('$g'), Vs).

g(X) :- ground(X).

%   bi_bind(+AbstractGoal): bind the outputs the builtin makes ground.
bi_bind(G) :- var(G), !.
bi_bind(_:G) :- !, bi_bind(G).
bi_bind(X is _) :- !, bind_g(X).
bi_bind(A = B) :- !, aunify(A, B).
bi_bind(functor(T, N, A)) :- !, ( g(T) -> bind_g(N-A) ; true ).
bi_bind(arg(N, T, A)) :- !, ( g(T) -> bind_g(N-A) ; true ).
bi_bind(T =.. L) :- !, ( g(T) -> bind_g(L) ; g(L) -> bind_g(T) ; true ).
bi_bind(copy_term(A, B)) :- !, ( g(A) -> bind_g(B) ; true ).
bi_bind(length(L, N)) :- !, bind_g(N), ( g(L) -> true ; true ).
bi_bind(G) :- functor(G, N, 2), text2(N), !, arg(1, G, A), arg(2, G, B),
    ( g(A) -> bind_g(B) ; g(B) -> bind_g(A) ; true ).
bi_bind(G) :- functor(G, N, 3), concat3(N), !, arg(1, G, A), arg(2, G, B), arg(3, G, C),
    ( g(A-B) -> bind_g(C) ; g(C) -> bind_g(A-B) ; true ).
bi_bind(atomic_list_concat(L, S)) :- !, ( g(L) -> bind_g(S) ; true ).
bi_bind(atomic_list_concat(L, Sep, S)) :- !, ( g(L-Sep) -> bind_g(S) ; g(Sep-S) -> bind_g(L) ; true ).
bi_bind(split_string(S, A, B, L)) :- !, ( g(S-A-B) -> bind_g(L) ; true ).
bi_bind(sub_atom(S, B, L, A, Sub)) :- !, ( g(S) -> bind_g(B-L-A-Sub) ; true ).
bi_bind(sub_string(S, B, L, A, Sub)) :- !, ( g(S) -> bind_g(B-L-A-Sub) ; true ).
bi_bind(format(Sink, _, _)) :- !, ( compound(Sink), arg(1, Sink, X) -> bind_g(X) ; true ).
bi_bind(with_output_to(Sink, _)) :- !, ( compound(Sink), arg(1, Sink, X) -> bind_g(X) ; true ).
bi_bind(member(X, L)) :- !, ( g(L) -> bind_g(X) ; true ).
bi_bind(memberchk(X, L)) :- !, ( g(L) -> bind_g(X) ; true ).
bi_bind(append(A, B, C)) :- !, ( g(A-B) -> bind_g(C) ; g(C) -> bind_g(A-B) ; true ).
bi_bind(append(L, C)) :- !, ( g(L) -> bind_g(C) ; true ).
bi_bind(select(X, L, R)) :- !, ( g(L) -> bind_g(X-R) ; true ).
bi_bind(selectchk(X, L, R)) :- !, ( g(L) -> bind_g(X-R) ; true ).
bi_bind(select(X, L, Y, R)) :- !, ( g(L-Y) -> bind_g(X-R) ; true ).
bi_bind(permutation(A, B)) :- !, ( g(A) -> bind_g(B) ; g(B) -> bind_g(A) ; true ).
bi_bind(nth0(I, L, E)) :- !, ( g(L) -> bind_g(I-E) ; true ).
bi_bind(nth1(I, L, E)) :- !, ( g(L) -> bind_g(I-E) ; true ).
bi_bind(nth0(I, L, E, R)) :- !, ( g(L) -> bind_g(I-E-R) ; true ).
bi_bind(nth1(I, L, E, R)) :- !, ( g(L) -> bind_g(I-E-R) ; true ).
bi_bind(last(L, E)) :- !, ( g(L) -> bind_g(E) ; true ).
bi_bind(between(_, _, X)) :- !, bind_g(X).
bi_bind(numlist(_, _, L)) :- !, bind_g(L).
bi_bind(succ(A, B)) :- !, bind_g(A-B).
bi_bind(plus(A, B, C)) :- !, bind_g(A-B-C).
bi_bind(term_to_atom(T, A)) :- !, ( g(T) -> bind_g(A) ; true ).
bi_bind(term_string(T, A)) :- !, ( g(T) -> bind_g(A) ; true ).
bi_bind(nb_getval(_, _)) :- !.
bi_bind(b_getval(_, _)) :- !.
bi_bind(G) :- functor(G, N, 2), list_fn(N), !, arg(1, G, A), arg(2, G, B),
    ( g(A) -> bind_g(B) ; true ).
bi_bind(G) :- functor(G, N, 3), list_fn3(N), !, arg(1, G, A), arg(2, G, B), arg(3, G, C),
    ( g(A-B) -> bind_g(C) ; true ).
bi_bind(sort(_, _, L, S)) :- !, ( g(L) -> bind_g(S) ; true ).
bi_bind(predsort(_, L, S)) :- !, ( g(L) -> bind_g(S) ; true ).
bi_bind(_).

text2(N) :- memberchk(N, [atom_codes, atom_chars, char_code, atom_number, number_codes,
                          number_chars, atom_string, string_chars, string_codes,
                          string_to_atom, number_string, upcase_atom, downcase_atom,
                          string_upper, string_lower, atom_length, string_length,
                          term_to_atom, string_code, text_to_string]).
concat3(N) :- memberchk(N, [atom_concat, string_concat]).
list_fn(N) :- memberchk(N, [msort, sort, keysort, reverse, list_to_set, sum_list, sumlist,
                            max_list, min_list, max_member, min_member, flatten,
                            exclude_dups, pairs_keys, pairs_values, length, last,
                            sum_list, list_to_ord_set, term_variables, copy_term,
                            transpose, max_list, min_list]).
list_fn3(N) :- memberchk(N, [subtract, intersection, union, delete, exclude, include,
                             pairs_keys_values, ord_union, ord_subtract, ord_intersection,
                             sumlist, max_member, min_member, nth0, nth1]).

aunify(A, B) :- var(A), !, ( var(B) -> A = B ; A = B -> true ; true ).
aunify(A, B) :- var(B), !, ( B = A -> true ; true ).
aunify('$g', B) :- !, bind_g(B).
aunify(A, '$g') :- !, bind_g(A).
aunify(A, B) :- compound(A), compound(B), functor(A, N, Ar), functor(B, N, Ar), !,
    A =.. [_|As], B =.. [_|Bs], maplist(aunify, As, Bs).
aunify(_, _).

%   bi_nondet(+AbstractGoal): the builtin can have several answers.
bi_nondet(G) :- var(G), !.
bi_nondet(_:G) :- !, bi_nondet(G).
bi_nondet(member(_, _)).
bi_nondet(between(_, _, X)) :- \+ g(X).
bi_nondet(append(A, _, C)) :- \+ g(A), \+ (g(C), fail).
bi_nondet(append(L, _)) :- \+ g(L).
bi_nondet(select(_, _, _)).
bi_nondet(select(_, _, _, _)).
bi_nondet(permutation(_, _)).
bi_nondet(nth0(I, _, _)) :- \+ g(I).
bi_nondet(nth1(I, _, _)) :- \+ g(I).
bi_nondet(nth0(I, _, _, _)) :- \+ g(I).
bi_nondet(nth1(I, _, _, _)) :- \+ g(I).
bi_nondet(length(L, N)) :- \+ g(L), \+ g(N).
bi_nondet(last(L, _)) :- \+ g(L).
bi_nondet(sub_atom(_, _, _, _, _)).
bi_nondet(sub_string(_, _, _, _, _)).
bi_nondet(atom_concat(A, B, _)) :- \+ g(A-B).
bi_nondet(string_concat(A, B, _)) :- \+ g(A-B).
bi_nondet(arg(N, _, _)) :- \+ g(N).
bi_nondet(clause(_, _)).
bi_nondet(retract(_)).
bi_nondet(current_op(_, _, _)).
bi_nondet(repeat).
bi_nondet(char_type(C, T)) :- \+ g(C-T).
bi_nondet(code_type(C, T)) :- \+ g(C-T).
bi_nondet(G) :- \+ bi_known(G).

bi_known(G) :- functor(G, N, A), ( det_bi(N/A) -> true ; nondet_bi(N/A) ).

nondet_bi(N/A) :- memberchk(N/A, [member/2, between/3, append/3, append/2, select/3, select/4,
    permutation/2, nth0/3, nth1/3, nth0/4, nth1/4, length/2, last/2, sub_atom/5,
    sub_string/5, atom_concat/3, string_concat/3, arg/3, clause/2, retract/1,
    current_op/3, repeat/0, char_type/2, code_type/2]).

det_bi(N/A) :- memberchk(N/A, [
    (is)/2, (=)/2, (\=)/2, (==)/2, (\==)/2, (@<)/2, (@>)/2, (@=<)/2, (@>=)/2, (<)/2,
    (>)/2, (=<)/2, (>=)/2, (=:=)/2, (=\=)/2, (=@=)/2, (\=@=)/2, var/1, nonvar/1, atom/1,
    number/1, integer/1, float/1, atomic/1, compound/1, callable/1, is_list/1, ground/1,
    string/1, is_dict/1, is_assoc/1, functor/3, (=..)/2, copy_term/2, atom_codes/2,
    atom_chars/2, char_code/2, atom_length/2, atom_number/2, number_codes/2,
    number_chars/2, atom_string/2, string_chars/2, string_codes/2, string_to_atom/2,
    string_length/2, number_string/2, term_to_atom/2, term_string/2, upcase_atom/2,
    downcase_atom/2, string_upper/2, string_lower/2, split_string/4,
    atomic_list_concat/2, atomic_list_concat/3, msort/2, sort/2, sort/4, predsort/3,
    keysort/2, reverse/2, list_to_set/2, sum_list/2, sumlist/2, max_list/2, min_list/2,
    max_member/2, min_member/2, numlist/3, memberchk/2, subtract/3, intersection/3,
    union/3, delete/3, exclude/3, include/3, partition/4, maplist/2, maplist/3,
    maplist/4, maplist/5, foldl/4, foldl/5, foldl/6, nb_getval/2, b_getval/2,
    nb_setval/2, b_setval/2, succ/2, plus/3, tab/1, tab/2, nl/0, nl/1, write/1, write/2,
    writeln/1, writeln/2, print/1, print/2, write_canonical/1, writeq/1, writeq/2,
    write_term/2, write_term/3, format/1, format/2, format/3, print_message/2,
    put_char/1, halt/0, halt/1, assert/1, asserta/1, assertz/1, retractall/1,
    flush_output/0, read_term/2, read_term/3, read/1, true/0, fail/0, false/0,
    term_variables/2, setarg/3, nb_setarg/3, string_code/3, selectchk/3, flatten/2,
    sum_list/2, list_to_ord_set/2, ord_union/3, ord_subtract/3, ord_intersection/3,
    ord_memberchk/2, pairs_keys_values/3, pairs_keys/2, pairs_values/2, transpose/2,
    with_output_to/2, findall/3, findall/4, aggregate_all/3, forall/2, (\+)/1, once/1,
    ignore/1, throw/1, tab/2, char_code/2, number_vars/3, numbervars/3, text_concat/3,
    get_time/1, statistics/2, random/1, random_between/3, garbage_collect/0,
    abolish_all_tables/0, succ_or_zero/1, text_to_string/2, sleep/1, shell/1, shell/2,
    getenv/2, setenv/2, atom_to_term/3, read_term_from_atom/3, sformat/3, format_atom/3,
    string/1, sub_atom_icasechk/3, nb_current/2, tab/1, last/2, length/2, sort/0,
    exclude/3, max_list/2, atomics_to_string/2, term_string/3, list_to_assoc/2,
    put_assoc/4, get_assoc/3, empty_assoc/1, assoc_to_list/2, assoc_to_keys/2,
    assoc_to_values/2, string_number/2, plus/3, abs/1, char_type/2, code_type/2,
    tabling/0, set_prolog_flag/2, op/3, garbage_collect/0, prompt/2, nb_setval/2]).

%   Builtins that cannot fail (once their arguments are as given): write and friends.
bi_total(G, _) :- functor(G, N, A), memberchk(N/A, [nl/0, nl/1, write/1, write/2, writeln/1,
    writeln/2, print/1, print/2, writeq/1, writeq/2, write_canonical/1, write_term/2,
    write_term/3, format/1, format/2, format/3, tab/1, tab/2, true/0, flush_output/0,
    print_message/2, nb_setval/2, assertz/1, asserta/1, assert/1, retractall/1]), !.
bi_total(X is _, Seen) :- var(X), \+ var_in(Seen, X), !.
bi_total(X = _, Seen) :- var(X), \+ var_in(Seen, X), !.
bi_total(_ = X, Seen) :- var(X), \+ var_in(Seen, X), !.

%   Side effects: anything that is observable outside the answer.
bi_effect(G) :- var(G), !.
bi_effect(_:G) :- !, bi_effect(G).
bi_effect(format(Sink, _, _)) :- !, \+ ( nonvar(Sink), Sink =.. [K, _], memberchk(K, [atom, string, codes, chars]) ).
bi_effect(with_output_to(_, G)) :- !, goal_effect_src(G).
bi_effect(G) :- functor(G, N, A), memberchk(N/A, [write/1, write/2, writeln/1, writeln/2,
    print/1, print/2, writeq/1, writeq/2, write_canonical/1, write_term/2, write_term/3,
    format/1, format/2, nl/0, nl/1, tab/1, tab/2, put_char/1, print_message/2, assert/1,
    asserta/1, assertz/1, retract/1, retractall/1, nb_setval/2, b_setval/2, nb_getval/2,
    b_getval/2, halt/0, halt/1, read/1, read_term/2, read_term/3, get_char/1,
    flush_output/0, set_prolog_flag/2, op/3, random/1, random_between/3, get_time/1,
    statistics/2, shell/1, shell/2, sleep/1, gensym/2, flag/3, setenv/2, nb_setarg/3,
    garbage_collect/0, abolish_all_tables/0, consult/1, prompt/2, nb_current/2,
    setarg/3]), !.
bi_effect(G) :- \+ bi_known(G), !.
bi_effect(G) :- meta_user_goals(G, Us), member(U-_, Us), ( var(U) -> true ; goal_effect_src(U) ), !.

%   user goals inside the meta-arguments of a builtin: Goal-ExtraArgs
meta_user_goals(G, Us) :-
    findall(U-N, meta_arg(G, U, N), Us).

meta_arg(G, U, N) :-
    callable(G), \+ G = b(_), \+ G = u(_),
    functor(G, F, A),
    meta_spec(F/A, Spec),
    arg(I, Spec, S), ( integer(S) -> N = S ; S == (^) -> N = 0 ; fail ),
    arg(I, G, Arg),
    strip_hats(Arg, U0, _),
    leaf_goal(U0, U).

meta_spec(F/A, Spec) :-
    functor(H, F, A),
    (   catch(predicate_property(system:H, meta_predicate(Spec)), _, fail) -> true
    ;   member(M, [lists, apply, aggregate, yall]),
        catch(predicate_property(M:H, meta_predicate(Spec)), _, fail) -> true
    ;   memberchk(F/A-Spec, [ aggregate_all/3-aggregate_all(?, 0, -),
                              aggregate_all/4-aggregate_all(?, ?, 0, -) ])
    ).

leaf_goal(V, V) :- var(V), !.
leaf_goal((A, B), L) :- !, ( leaf_goal(A, L) ; leaf_goal(B, L) ).
leaf_goal((A ; B), L) :- !, ( leaf_goal(A, L) ; leaf_goal(B, L) ).
leaf_goal((A -> B), L) :- !, ( leaf_goal(A, L) ; leaf_goal(B, L) ).
leaf_goal((A *-> B), L) :- !, ( leaf_goal(A, L) ; leaf_goal(B, L) ).
leaf_goal(\+ A, L) :- !, leaf_goal(A, L).
leaf_goal(_:A, L) :- !, leaf_goal(A, L).
leaf_goal(G, L) :- has_meta(G), !, meta_arg(G, L, _).
leaf_goal(G, G).

has_meta(G) :- meta_arg(G, _, _), !.

goal_effect_src(G) :- var(G), !.
goal_effect_src(G) :- leaf_goal(G, L), ( var(L) -> true ; user_goal(L) -> key(L, K), eff_key(K)
                                          ; L \== G, bi_effect(L) ; L == G, bi_effect_leaf(L) ), !.

bi_effect_leaf(G) :- \+ user_goal(G), bi_effect(G).

test_bi(T) :- callable(T), functor(T, N, A), memberchk(N/A, [(<)/2, (>)/2, (=<)/2, (>=)/2,
    (=:=)/2, (=\=)/2, (==)/2, (\==)/2, (@<)/2, (@>)/2, (@=<)/2, (@>=)/2, (\=)/2,
    integer/1, atom/1, number/1, atomic/1, is_list/1, compound/1, string/1, float/1,
    callable/1]).

complementary(X, Y) :- ( compl(X, Y) -> true ; compl(Y, X) ).

compl(A < B, C >= D) :- A == C, B == D.
compl(A > B, C =< D) :- A == C, B == D.
compl(A < B, C =< D) :- A == D, B == C.
compl(A > B, C >= D) :- A == D, B == C.
compl(A =:= B, C =\= D) :- A == C, B == D.
compl(A == B, C \== D) :- A == C, B == D.

safe_test(G) :- catch(G, _, true).

                 /*******************************
                 *        MODE ANALYSIS         *
                 *******************************/

%   One call pattern per predicate (g: ground, f: a fresh variable, a: anything) and one
%   success pattern (g or a per argument), by abstract interpretation to a fixpoint.

modes :-
    retractall(m_pat(_, _)), retractall(m_succ(_, _)), retractall(callable_key(_)),
    forall(conv_key(K), ( assertz(m_pat(K, none)), assertz(m_succ(K, none)) )),
    forall(kept(K, _), ( K = _/A, length(P, A), maplist(=(a), P),
                         assertz(m_pat(K, P)), assertz(m_succ(K, P)),
                         assertz(callable_key(K)) )),
    forall(kept(K, _), kept_sites(K)),
    entries,
    mode_loop,
    (   conv_key(K), m_pat(K, none)
    ->  K = _/A, length(P, A), maplist(=(a), P),
        pat_lub(K, P), mode_loop2
    ;   true
    ).

mode_loop2 :-
    mode_loop,
    (   conv_key(K), m_pat(K, none)
    ->  K = _/A, length(P, A), maplist(=(a), P), pat_lub(K, P), mode_loop2
    ;   true
    ).

kept_sites(K) :-
    src_clauses(K, Cls),
    forall(( member((_ :- B), Cls), leaf_goal(B, L), nonvar(L), user_goal(L) ),
           ( key(L, LK), all_a(LK, P), pat_lub(LK, P), assertz(callable_key(LK)) )).

all_a(_/A, P) :- length(P, A), maplist(=(a), P).

entries :-
    retractall(has_caller(_)),
    forall(( conv_key(K), ncls(K, Cls), member(cl(_, Kind), Cls), kind_goals(Kind, Gs),
             member(G, Gs), called_key(G, CK), CK \== K ),
           assertz(has_caller(CK))),
    forall(( kept(K, _), src_clauses(K, Cls), member((_ :- B), Cls),
             leaf_goal(B, L), nonvar(L), user_goal(L), key(L, CK), CK \== K ),
           assertz(has_caller(CK))),
    forall(entry(N, _), ( conv_key(N/0) -> pat_lub(N/0, []) ; true )),
    forall(directive_goal(G), entry_goal(G)),
    forall(( export_key(K), conv_key(K), \+ entry(_, _) ),
           ( all_a(K, P), pat_lub(K, P), assertz(callable_key(K)) )),
    forall(( conv_key(K), \+ aux_of(K, _), \+ has_caller(K), \+ entry(_, _) ),
           ( all_a(K, P), pat_lub(K, P), assertz(callable_key(K)) )).

called_key(u(G), K) :- key(G, K).
called_key(not(S), K) :- called_key(S, K).
called_key(once(S), K) :- called_key(S, K).
called_key(ignore(S), K) :- called_key(S, K).
called_key(findall(_, S, _), K) :- called_key(S, K).
called_key(findall4(_, S, _, _), K) :- called_key(S, K).
called_key(aggr(_, _, S, _), K) :- called_key(S, K).
called_key(b(G), K) :- meta_user_goals(G, Us), member(U-N, Us), nonvar(U),
    callable(U), functor(U, F, A0), A is A0 + N, pred_key(F/A, _), K = F/A.

directive_goal(G) :-
    src_file(_, P), db_get(item, P, it(_, dir(D, _), _)),
    init_goal(D, G).

init_goal(initialization(G), G).
init_goal(initialization(G, _), G).

%   a directive's goal: ordinary Prolog calls the predicates in it by name
entry_goal(G) :-
    forall(( leaf_goal(G, L), nonvar(L), user_goal(L) ),
           ( key(L, K), site_pat(L, [], P), pat_lub(K, P), assertz(callable_key(K)) )).

mode_loop :-
    nb_setval(pl2detlog_changed, false),
    forall(( m_pat(K, P), P \== none, conv_key(K) ), analyse_pred(K, P)),
    (   nb_getval(pl2detlog_changed, true) -> mode_loop ; true ).

analyse_pred(K, P) :-
    ncls(K, Cls),
    forall(member(Cl, Cls),
           ( abstract_clause(Cl, P, S) -> succ_lub(K, S) ; true )).

abstract_clause(cl(H, Kind), P, Succ) :-
    copy_term(H-Kind, H1-Kind1),
    kind_goals(Kind1, Gs),
    H1 =.. [_|As],
    maplist(apply_pat, As, P),
    seen_init(As, P, S0),
    awalk(Gs, S0, reg, _),
    maplist(arg_succ, As, Succ).

kind_goals(plain(Gs), Gs).
kind_goals(commit(G, B), Gs) :- append(G, B, Gs).

apply_pat(A, g) :- !, bind_g(A).
apply_pat(_, _).

arg_succ(A, g) :- ground(A), !.
arg_succ(_, a).

%   Variables that may already be bound: every head variable but a fresh one at an f position.
seen_init(As, P, Seen) :-
    term_variables(As, Vs),
    exclude(fresh_head_var_(As, P), Vs, Seen).

fresh_head_var_(As, P, V) :- fresh_head_var(V, As, P).

fresh_head_var(V, As, P) :-
    nth1(I, As, A), A == V, nth1(I, P, f),
    occurrences(V, As, 1).

occurrences(V, T, N) :- term_variables_list(T, L), include(==(V), L, Os), length(Os, N).

term_variables_list(T, L) :- phrase(tvl(T), L).
tvl(V) --> { var(V) }, !, [V].
tvl(T) --> { compound(T) }, !, { T =.. [_|As] }, tvls(As).
tvl(_) --> [].
tvls([]) --> [].
tvls([A|As]) --> tvl(A), tvls(As).

seen_add(G, S0, S) :- term_variables(G-S0, S).

%   awalk(+Goals, +Seen0, +Reg, -Seen): fails when a goal can have no answer.
awalk([], S, _, S).
awalk([G|Gs], S0, R, S) :- agoal(G, S0, R, S1), awalk(Gs, S1, R, S).

agoal('$cut', S, _, S) :- !.
agoal(b(G), S0, R, S) :- !,
    ( R == reg -> meta_sites(G) ; true ),
    bi_bind(G), seen_add(G, S0, S).
agoal(u(G), S0, R, S) :- !,
    key(G, K),
    ( R == reg -> site_pat(G, S0, P), pat_lub(K, P) ; true ),
    succ_of(K, Succ), Succ \== none,
    G =.. [_|As], maplist(apply_succ, As, Succ),
    seen_add(G, S0, S).
agoal(not(Sg), S0, R, S0) :- !, asite(Sg, S0, R).
agoal(once(Sg), S0, R, S) :- !, agoal(Sg, S0, R, S).
agoal(ignore(Sg), S0, R, S) :- !, asite(Sg, S0, R), seen_add(Sg, S0, S).
agoal(findall(T, Sg, L), S0, R, S) :- !, afind(T, Sg, L, S0, R), seen_add(L, S0, S).
agoal(findall4(T, Sg, L, T0), S0, R, S) :- !,
    afind(T, Sg, L0, S0, R), ( g(L0-T0) -> bind_g(L) ; true ), seen_add(L-L0, S0, S).
agoal(aggr(F, E, Sg, Res), S0, R, S) :- !,
    (   memberchk(F, [count, sum, max, min]) -> asite(Sg, S0, R), bind_g(Res)
    ;   afind(E, Sg, Res, S0, R)
    ),
    seen_add(Res, S0, S).

afind(T, Sg, L, S0, R) :-
    asite(Sg, S0, R),
    copy_term(T-Sg, T2-Sg2),
    (   agoal(Sg2, S0, noreg, _) -> ( g(T2) -> bind_g(L) ; true ) ; bind_g(L) ).

asite(b(G), _, R) :- !, ( R == reg -> meta_sites(G) ; true ).
asite(u(G), S0, R) :- !, ( R == reg -> key(G, K), site_pat(G, S0, P), pat_lub(K, P) ; true ).
asite(_, _, _).

meta_sites(G) :-
    forall(( meta_user_goals(G, Us), member(U-N, Us), nonvar(U), callable(U),
             functor(U, F, A0), A is A0 + N, pred_key(F/A, _) ),
           ( all_a(F/A, P), pat_lub(F/A, P), assertz(callable_key(F/A)) )).

apply_succ(A, g) :- !, bind_g(A).
apply_succ(_, _).

succ_of(K, S) :- ( m_succ(K, S0) -> S = S0 ; K = _/A, length(S, A), maplist(=(a), S) ).

site_pat(G, Seen, P) :-
    G =.. [_|As],
    maplist(site_arg(As, Seen), As, P).

site_arg(_, _, A, g) :- ground(A), !.
site_arg(As, Seen, A, f) :- var(A), \+ var_in(Seen, A), occurrences(A, As, 1), !.
site_arg(_, _, _, a).

pat_lub(K, P) :-
    (   m_pat(K, Old) -> true ; Old = none ),
    lub(Old, P, New),
    (   New == Old -> true
    ;   retractall(m_pat(K, _)), assertz(m_pat(K, New)), nb_setval(pl2detlog_changed, true)
    ).

succ_lub(K, S) :-
    (   m_succ(K, Old) -> true ; Old = none ),
    lub(Old, S, New),
    (   New == Old -> true
    ;   retractall(m_succ(K, _)), assertz(m_succ(K, New)), nb_setval(pl2detlog_changed, true)
    ).

lub(none, P, P) :- !.
lub(P, none, P) :- !.
lub(P, Q, R) :- maplist(lub1, P, Q, R).
lub1(X, X, X) :- !.
lub1(_, _, a).

                 /*******************************
                 *    EFFECTS AND DETERMINISM   *
                 *******************************/

effects :-
    retractall(eff_key(_)),
    forall(kept(K, _), assertz(eff_key(K))),
    eff_loop.

eff_loop :-
    nb_setval(pl2detlog_changed, false),
    forall(( conv_key(K), \+ eff_key(K), ncls(K, Cls), member(cl(_, Kind), Cls),
             kind_goals(Kind, Gs), member(G, Gs), goal_eff(G) ),
           ( eff_key(K) -> true ; assertz(eff_key(K)), nb_setval(pl2detlog_changed, true) )),
    (   nb_getval(pl2detlog_changed, true) -> eff_loop ; true ).

%   predicates that can have infinitely many answers (a builtin generator without end)
infinite :-
    retractall(inf_key(_)),
    inf_loop.

inf_loop :-
    nb_setval(pl2detlog_changed, false),
    forall(( conv_key(K), \+ inf_key(K), ncls(K, Cls), member(cl(_, Kind), Cls),
             kind_goals(Kind, Gs), member(G, Gs), goal_inf(G) ),
           ( inf_key(K) -> true ; assertz(inf_key(K)), nb_setval(pl2detlog_changed, true) )),
    (   nb_getval(pl2detlog_changed, true) -> inf_loop ; true ).

goal_inf(b(G)) :- infinite_gen(G).
goal_inf(u(G)) :- key(G, K), inf_key(K).

infinite_gen(between(_, H, _)) :- ( H == inf ; H == infinite ).
infinite_gen(repeat).

goal_eff(b(G)) :- bi_effect(G).
goal_eff(u(G)) :- key(G, K), eff_key(K).
goal_eff(not(S)) :- goal_eff(S).
goal_eff(once(S)) :- goal_eff(S).
goal_eff(ignore(S)) :- goal_eff(S).
goal_eff(findall(_, S, _)) :- goal_eff(S).
goal_eff(findall4(_, S, _, _)) :- goal_eff(S).
goal_eff(aggr(_, _, S, _)) :- goal_eff(S).

%   Greatest fixpoint: assume every predicate is deterministic, drop those that are not.
dets :-
    retractall(det_key(_)),
    forall(( conv_key(K), m_pat(K, P), P \== none ), assertz(det_key(K))),
    det_loop.

det_loop :-
    nb_setval(pl2detlog_changed, false),
    forall(det_key(K),
           (   det_check(K) -> true
           ;   retract(det_key(K)), nb_setval(pl2detlog_changed, true)
           )),
    (   nb_getval(pl2detlog_changed, true) -> det_loop ; true ).

det_check(K) :-
    m_pat(K, P),
    resolved(K, Rs),
    det_pairs(Rs, P),
    forall(member(r(H, Kind), Rs), det_body(H, Kind, P)).

det_pairs([], _).
det_pairs([R|Rs], P) :-
    forall(member(R2, Rs), ( R = r(_, commit(_, _)) -> true ; exclusive(R, R2, P, _) )),
    det_pairs(Rs, P).

det_body(H, plain(Gs), P) :- annotate(H, Gs, P, As), forall(member(A, As), arg(2, A, true)).
det_body(H, commit(G, B), P) :-
    append(G, B, Gs), annotate(H, Gs, P, As),
    length(G, NG), length(Pre, NG), append(Pre, Post, As),
    forall(member(A, Post), arg(2, A, true)).

%   resolved(+K, -Rs): the clauses, with each unnecessary cut removed.
resolved(K, Rs) :-
    m_pat(K, P),
    ncls(K, Cls),
    resolve_cuts(Cls, P, Rs).

resolve_cuts([], _, []).
resolve_cuts([cl(H, Kind)|Cs], P, [r(H, Kind1)|Rs]) :-
    (   Kind = commit(G, B), cut_unnecessary(H, G, Cs, P)
    ->  append(G, B, Gs), Kind1 = plain(Gs)
    ;   Kind1 = Kind
    ),
    resolve_cuts(Cs, P, Rs).

cut_unnecessary(H, G, Later, P) :-
    annotate(H, G, P, As),
    forall(member(A, As), arg(2, A, true)),
    forall(member(cl(H2, K2), Later), exclusive(r(H, commit(G, [])), r(H2, K2), P, _)).

%   exclusive(+R1, +R2, +P, -How): no call with pattern P can enter both clauses.
exclusive(r(H1, K1), r(H2, K2), P, How) :-
    lead_tests(K1, T1), lead_tests(K2, T2),
    copy_term(H1-T1, A1-U1), copy_term(H2-T2, A2-U2),
    A1 =.. [_|As1], A2 =.. [_|As2],
    (   g_clash(As1, As2, P, How)
    ->  true
    ;   form(mnn),
        g_unify(As1, As2, P),
        (   member(b(T), U1), ground(T), \+ safe_test(T)
        ;   member(b(T), U2), ground(T), \+ safe_test(T)
        ;   member(b(X), U1), member(b(Y), U2), complementary(X, Y)
        )
    ->  How = guard
    ).

g_clash(As1, As2, P, How) :-
    nth1(I, P, g), nth1(I, As1, X), nth1(I, As2, Y),
    \+ X = Y, !,
    ( I == 1 -> How = index ; How = guard ).

g_unify([], [], []).
g_unify([X|Xs], [Y|Ys], [M|Ms]) :-
    ( M == g -> X = Y ; true ),
    g_unify(Xs, Ys, Ms).

lead_tests(plain(Gs), Ts) :- lead_tests_(Gs, Ts).
lead_tests(commit(G, _), Ts) :- lead_tests_(G, Ts).
lead_tests_([b(T)|Gs], [b(T)|Ts]) :- test_bi(T), !, lead_tests_(Gs, Ts).
lead_tests_(_, []).

%   annotate(+Head, +Goals, +Pattern, -Anns): an(Goal, Det, Total, GroundBefore, InnerDet)
annotate(H, Gs, P, Anns) :-
    term_variables(H-Gs, OVs),
    copy_term(H-Gs-OVs, H1-Gs1-CVs),
    H1 =.. [_|As],
    maplist(apply_pat, As, P),
    seen_init(As, P, S0),
    ann_walk(Gs, Gs1, OVs, CVs, S0, Anns0),
    add_shared(Anns0, H, [], Anns).

%   an(Goal, Det, Total, GroundBefore, InnerDet, Shared): Shared are the goal's variables that
%   occur elsewhere in the clause
add_shared([], _, _, []).
add_shared([an(G, D, T, GB, ID)|As], H, Before, [an(G, D, T, GB, ID, Sh)|Rs]) :-
    rest_goals(As, After),
    term_variables(H-Before-After, O),
    term_variables(G, GV),
    shared_vars(GV, O, Sh),
    add_shared(As, H, [G|Before], Rs).

ann_walk([], [], _, _, _, []).
ann_walk([G|Gs], [A|As], OVs, CVs, S0, [an(G, Det, Total, GB, ID)|Rest]) :-
    ground_before(OVs, CVs, GB),
    goal_det(A, Det), inner_det(A, ID),
    ( A = b(AG), bi_total(AG, S0) -> Total = true ; Total = false ),
    (   agoal(A, S0, noreg, S1)
    ->  ann_walk(Gs, As, OVs, CVs, S1, Rest)
    ;   maplist(unreached, Gs, Rest)
    ).

unreached(G, an(G, true, false, [], true)).  % add_shared adds the 6th argument

ground_before([], [], []).
ground_before([O|Os], [C|Cs], GB) :-
    ( ground(C) -> GB = [O|GB1] ; GB = GB1 ),
    ground_before(Os, Cs, GB1).

goal_det(b(G), D) :- !, ( bi_nondet(G) -> D = false ; D = true ).
goal_det(u(G), D) :- !, key(G, K), ( det_key(K) -> D = true ; D = false ).
goal_det(_, true).

inner_det(G, D) :- inner(G, S), !, goal_det(S, D).
inner_det(_, true).

inner(not(S), S).
inner(once(S), S).
inner(ignore(S), S).
inner(findall(_, S, _), S).
inner(findall4(_, S, _, _), S).
inner(aggr(_, _, S, _), S).

                 /*******************************
                 *       MNN SOURCE REWRITES    *
                 *******************************/

%   Accumulate an appended result:  p([], []).  p([H|T], R) :- p(T, RT), append(RT, E, R).
%   With acc(L, A) = p(L) ++ A:  acc([], A) = A  and  acc([H|T], A) = acc(T, E ++ A), by the
%   associativity of ++; so p(L) = acc(L, []) for every proper list L (a ground first argument).
accumulate :-
    forall(( conv_key(K), K = Name/2, m_pat(K, [g, _]), ncls(K, [C1, C2]),
             acc_shape(K, C1, C2, H, T, E) ),
           acc_rewrite(Name, H, T, E)).

acc_shape(Name/2, cl(B, plain([])), cl(Hd, plain([u(Rec), App])), H, T, E) :-
    B =.. [Name, [], []],
    Hd =.. [Name, [H|T], R],
    Rec =.. [Name, T1, RT], T1 == T,
    app_goal(App, RT1, E, R1), RT1 == RT, R1 == R,
    var(H), var(T), var(R), var(RT),
    term_variables(E, EV),
    forall(member(V, EV), V == H).

app_goal(b(append(A, B, C)), A, B, C).
app_goal(u(G), A, B, C) :- G =.. [F, A, B, C], is_append(F/3).

is_append(K) :-
    ncls(K, [cl(H1, plain([])), cl(H2, plain([u(R)]))]),
    K = F/3,
    H1 =.. [F, [], L1, L2], L1 == L2, var(L1),
    H2 =.. [F, [X|Xs], Y, [X1|Zs]], X == X1,
    R =.. [F, Xs1, Y1, Zs1], Xs1 == Xs, Y1 == Y, Zs1 == Zs,
    var(X), var(Xs), var(Y), var(Zs).

acc_rewrite(Name, _, _, _) :-
    format(atom(AN), '~w__acc', [Name]),
    retractall(dbv(ncl, Name/2, _, _, _)),
    fresh('L', L), fresh('R', R),
    H0 =.. [Name, L, R], C0 =.. [AN, L, [], R],
    db_put(ncl, Name/2, cl(H0, plain([u(C0)]))),
    aggregate_all(count, pred_key(_, _), I),
    assertz(pred_key(AN/3, I)), assertz(aux_of(AN/3, Name/2)), assertz(aux_root(AN/3, Name/2)),
    fresh('A', A), B1 =.. [AN, [], A, A],
    db_put(ncl, AN/3, cl(B1, plain([]))),
    fail.
acc_rewrite(Name, H, T, E) :-
    format(atom(AN), '~w__acc', [Name]),
    fresh('A', A), fresh('R', R),
    (   is_list(E) -> append(E, A, A1), Pre = []
    ;   fresh('A1', A1), Pre = [b(append(E, A, A1))]
    ),
    H2 =.. [AN, [H|T], A, R], Rec =.. [AN, T, A1, R],
    append(Pre, [u(Rec)], Gs),
    db_put(ncl, AN/3, cl(H2, plain(Gs))),
    format(atom(N), 'MNN accumulate: ~w(L) ++ A = ~w(L, A), so ~w(L) = ~w(L, []) (++ is associative; L is a proper list, ground at every call)', [Name, AN, Name, AN]),
    assertz(note(Name/2, N)).

%   UNFOLD: a call of a predicate with one clause whose body is pure builtins and whose head
%   arguments are distinct variables is that body (the clause, renamed, in its place).
unfold :-
    findall(K, ( conv_key(K), unfoldable(K) ), Us),
    forall(( conv_key(K), \+ memberchk(K, Us), ncls(K, Cls),
             member(cl(_, Kd), Cls), kind_goals(Kd, Gs), member(u(G), Gs),
             key(G, GK), memberchk(GK, Us) ),
           true),
    forall(( conv_key(K), \+ memberchk(K, Us) ), unfold_pred(K, Us)).

unfoldable(K) :-
    \+ entry(_, _) -> fail ;
    ncls(K, [cl(H, plain(Gs))]), Gs \== [],
    forall(member(G, Gs), ( G = b(B), \+ bi_effect(B), bi_nondet(B) -> true ; G = b(B), \+ bi_effect(B) )),
    member(b(B0), Gs), bi_nondet(B0), !,
    H =.. [_|As], is_set_vars(As).

unfold_pred(K, Us) :-
    ncls(K, Cls),
    maplist(unfold_clause(Us, K), Cls, Cls1),
    (   Cls1 == Cls -> true
    ;   retractall(dbv(ncl, K, _, _, _)),
        forall(member(C, Cls1), db_put(ncl, K, C))
    ).

unfold_clause(Us, K, cl(H, plain(Gs)), cl(H, plain(Gs1))) :- !, unfold_goals(Gs, Us, K, Gs1).
unfold_clause(Us, K, cl(H, commit(G, B)), cl(H, commit(G1, B1))) :-
    unfold_goals(G, Us, K, G1), unfold_goals(B, Us, K, B1).

unfold_goals([], _, _, []).
unfold_goals([u(G)|Gs], Us, K, Out) :-
    key(G, GK), memberchk(GK, Us), !,
    ncls(GK, [cl(H, plain(Body))]),
    H = G,
    (   note(K, N), sub_atom(N, 0, _, _, 'MNN unfold') -> true
    ;   format(atom(N), 'MNN unfold: ~q has one clause of pure builtins, so its body is written in place of the call', [GK]),
        assertz(note(K, N))
    ),
    append(Body, Rest, Out),
    unfold_goals(Gs, Us, K, Rest).
unfold_goals([G|Gs], Us, K, [G|Rest]) :- unfold_goals(Gs, Us, K, Rest).

%   MEMO: a deterministic, pure, tree-recursive predicate called with ground inputs and
%   fresh outputs is tabled.  Its one answer per call is a function of the call.
memo :-
    forall(( det_key(K), \+ eff_key(K), m_pat(K, P), \+ memberchk(a, P), memberchk(g, P),
             tree_recursive(K) ),
           ( assertz(table_key(K)),
             format(atom(N), 'MNN memo: pure and deterministic with ground inputs (~w), so each call has one answer: tabled', [P]),
             assertz(note(K, N)) )).

tree_recursive(K) :-
    ncls(K, Cls), member(cl(_, Kind), Cls), kind_goals(Kind, Gs),
    include(self_call(K), Gs, Calls), length(Calls, N), N >= 2, !.

self_call(K, u(G)) :- key(G, K).

                 /*******************************
                 *          CONVERSION          *
                 *******************************/

convert_form(Form) :-
    reset_form,
    assertz(form(Form)),
    normalise,
    (   Form == mnn -> unfold ; true ),
    modes, effects, infinite, dets,
    (   Form == mnn
    ->  accumulate,
        (   note(_, _) -> modes, effects, infinite, dets ; true ),
        memo
    ;   true
    ),
    plan.

%   Which versions are needed: what ordinary Prolog calls by name, and what that code calls.
plan :-
    forall(callable_key(K), need_key(K, prolog)),
    forall(entry(Name, _), need_key(Name/0, entry)),
    gen_loop,
    (   entry(_, _)
    ->  true
    ;   forall(( pred_key(K, _), \+ aux_of(K, _), conv_key(K),
                 \+ dbv(out, K-det, _, _, _), \+ dbv(out, K-prolog, _, _, _) ),
               ( assertz(note(K, 'as written too, so that it can be called by name')),
                 assertz(done(K, prolog)), gen_kept(K) )),
        gen_loop
    ),
    forall(( pred_key(K, _), \+ aux_of(K, _), \+ dbv(out, K-_, _, _, _) ),
           ( src_clauses(K, Cls), forall(member(C, Cls), out(K, dead, C)) )).

need_key(K, M) :- ( need(K, M) -> true ; assertz(need(K, M)) ).

gen_loop :-
    (   need(K, M), \+ done(K, M)
    ->  assertz(done(K, M)),
        catch(gen(K, M), E, gen_failed(K, M, E)),
        gen_loop
    ;   true
    ).

gen_failed(K, M, E) :-
    retractall(dbv(out, K-M, _, _, _)),
    format(user_error, "% pl2detlog: ~q (~w version) kept as Prolog: ~q~n", [K, M, E]),
    assertz(note(K, 'kept as Prolog: this version could not be converted')),
    (   done(K, prolog) -> true ; assertz(done(K, prolog)), gen_kept(K) ).

%   gen(+Key, +Mode): write the clauses of one version into dbv(out, Key-Mode, Clause).
gen(K, prolog) :- !,
    (   kept(K, _) -> gen_kept(K)
    ;   pred_key(K, _), \+ m_pat(K, _) -> gen_kept(K)
    ;   det_key(K) -> need_key(K, det)
    ;   eff_key(K) -> gen_kept(K)
    ;   inf_key(K) -> gen_kept(K)
    ;   need_key(K, all), gen_wrapper(K)
    ).
gen(K, entry) :- !, gen_entry(K).
gen(K, det) :- !, gen_det(K).
gen(K, first) :- !, gen_first(K).
gen(K, all) :- !, gen_all(K).

out(K, M, Cl) :- copy_term(Cl, Cl1), db_put(out, K-M, Cl1).

gen_kept(K) :-
    prolog_clauses(K, Cls),
    forall(member(C, Cls), out(K, prolog, C)),
    forall(( member((_ :- B), Cls), leaf_goal(B, L), nonvar(L), user_goal(L) ),
           ( key(L, LK), need_key(LK, prolog) )).

gen_wrapper(K) :-
    K = N/A, length(Ps, A), name_params(K, Ps),
    H =.. [N|Ps], all_name(K, AN),
    fresh('As', As),
    append(Ps, [As, []], AA), C =.. [AN|AA],
    out(K, prolog, (H :- C, dl_member(H, As))).

all_name(N/_, AN) :- atom_concat(N, '__all', AN).
first_name(N/_, FN) :- atom_concat(N, '__first', FN).

name_params(K, Ps) :-
    (   ncls(K, [cl(H, _)|_]), H =.. [_|As] -> maplist(param_name, As, Ps) ; true ),
    (   ncls(K, Cls) -> term_variables(Cls, CVs), maplist(var_hint, CVs, Used) ; Used = [] ),
    distinct_names(Ps, Used, [], _).

%   distinct_names(+Vars, +UsedHints, +Taken0, -Taken): every variable gets its own name;
%   one with no name, or with a name taken by an earlier one, gets a free letter
distinct_names([], _, T, T).
distinct_names([V|Vs], Used, T0, T) :-
    (   get_attr(V, pl2detlog, N), N \== '', \+ memberchk(N, T0), \+ sub_atom(N, 0, 1, _, '_')
    ->  true
    ;   member(N, ['X', 'Y', 'Z', 'W', 'V', 'U', 'S', 'R', 'Q', 'P', 'M', 'K', 'J']),
        \+ memberchk(N, Used), \+ memberchk(N, T0)
    ->  put_attr(V, pl2detlog, N)
    ;   length(T0, I0), I is I0 + 1, format(atom(N), 'A~w', [I]), put_attr(V, pl2detlog, N)
    ),
    distinct_names(Vs, Used, [N|T0], T).

param_name(A, P) :- ( var(A), get_attr(A, pl2detlog, N) -> fresh(N, P) ; true ).
numbered_params([], _).
numbered_params([P|Ps], I) :-
    ( get_attr(P, pl2detlog, _) -> true ; format(atom(N), 'A~w', [I]), fresh(N, P) ),
    I1 is I + 1, numbered_params(Ps, I1).

%   the clauses of K as ordinary Prolog: the source, or for an auxiliary predicate its
%   normalised clauses written back
prolog_clauses(K, Cls) :-
    (   aux_of(K, _)
    ->  ncls(K, NCls), maplist(denorm_clause, NCls, Cls)
    ;   src_clauses(K, Cls)
    ).

denorm_clause(cl(H, plain(Gs)), (H :- B)) :- denorm_goals(Gs, B).
denorm_clause(cl(H, commit(G, Bd)), (H :- B)) :-
    append(G, ['$cut'|Bd], Gs), denorm_goals(Gs, B).

denorm_goals([], true).
denorm_goals([G], B) :- !, denorm(G, B).
denorm_goals([G|Gs], (B, Bs)) :- denorm(G, B), denorm_goals(Gs, Bs).

denorm('$cut', !).
denorm(b(G), G).
denorm(u(G), G).
denorm(not(S), \+ G) :- denorm(S, G).
denorm(once(S), once(G)) :- denorm(S, G).
denorm(ignore(S), ignore(G)) :- denorm(S, G).
denorm(findall(T, S, L), findall(T, G, L)) :- denorm(S, G).
denorm(findall4(T, S, L, T0), findall(T, G, L, T0)) :- denorm(S, G).
denorm(aggr(F, E, S, R), aggregate_all(Spec, G, R)) :-
    denorm(S, G), ( F == count -> Spec = count ; Spec =.. [F, E] ).

%   the entry: Name :- the first answer of the query.
gen_entry(K) :-
    (   kept(K, _) -> need_key(K, prolog)
    ;   det_key(K) -> need_key(K, det)
    ;   K = N/_, gen_first(K, N, entry)
    ).

ctx(K, M, c(K, M)).

%   ---- det version: same name, clauses told apart by a bound first argument ----
gen_det(K) :-
    resolved(K, Rs), m_pat(K, P),
    ctx(K, det, Ctx),
    (   table_key(K) -> K = N/A, out(K, det, (:- table(N/A))) ; true ),
    det_groups(Rs, P, Groups),
    forall(member(Gr, Groups), det_group(Gr, K, P, Ctx)).

%   Clauses told apart by a ground argument: the first argument where the call is ground
%   and every head has a functor, with two functors or more.  SWI-Prolog indexes that
%   argument, so each group is entered without a choicepoint.
det_groups(Rs, P, Groups) :-
    Rs = [_, _|_],
    nth1(I, P, g),
    forall(member(r(H, _), Rs), ( arg(I, H, A), nonvar(A) )),
    findall(F, ( member(r(H, _), Rs), arg(I, H, A), first_functor(A, F) ), Fs0),
    list_to_set(Fs0, Fs), Fs = [_, _|_], !,
    findall(Gr, ( member(F, Fs), include(has_functor(I, F), Rs, Gr) ), Groups).
det_groups(Rs, _, [Rs]).

first_functor(A, F) :- ( atomic(A) -> F = A ; functor(A, N, Ar), F = N/Ar ).
has_functor(I, F, r(H, _)) :- arg(I, H, A), first_functor(A, F).

det_group([r(H, Kind)], K, P, Ctx) :- !,
    det_clause_body(H, Kind, P, Ctx, Body),
    out(K, det, (H :- Body)).
det_group(Rs, K, P, Ctx) :-
    group_head(Rs, K, Head),
    det_chain(Rs, Head, P, Ctx, Body),
    out(K, det, (Head :- Body)).

det_clause_body(H, plain(Gs), P, Ctx, Body) :-
    annotate(H, Gs, P, As), tr_det(As, Ctx, Body).
det_clause_body(H, commit(G, B), P, Ctx, Body) :-
    append(G, B, Gs), annotate(H, Gs, P, As),
    length(G, NG), length(AG, NG), append(AG, AB, As),
    term_variables(H-B, After),
    tr_first(AG, After, Ctx, GC), tr_det(AB, Ctx, BC),
    conj(GC, BC, Body).

%   a chain of clauses with the same first-argument functor
det_chain([r(H, Kind)], Head, P, Ctx, Code) :- !,
    copy_term(H-Kind, H1-Kind1),
    head_match(Head, H1, U),
    kind_goals(Kind1, _),
    det_clause_body(H1, Kind1, P, Ctx, B),
    unif_goals(U, UC), conj(UC, B, Code).
det_chain([r(H, Kind)|Rs], Head, P, Ctx, if_commit(Cond, Then, Else)) :-
    copy_term(H-Kind, H1-Kind1),
    head_match(Head, H1, U),
    (   Kind1 = commit(G, B)
    ->  append(G, B, Gs), annotate(H1, Gs, P, As),
        length(G, NG), length(AG, NG), append(AG, AB, As),
        term_variables(Head-U-B, After),
        tr_first(AG, After, Ctx, CG), tr_det(AB, Ctx, TB)
    ;   Kind1 = plain(Gs),
        annotate(H1, Gs, P, As),
        lead_tests(plain(Gs), Ts), length(Ts, NT), length(AT, NT), append(AT, AB, As),
        tr_det(AT, Ctx, CG), tr_det(AB, Ctx, TB)
    ),
    split_unifs(U, Head, P, CG, UC, UT),
    unif_goals(UC, UCC), unif_goals(UT, UTC),
    conj(UCC, CG, Cond), conj(UTC, TB, Then),
    det_chain(Rs, Head, P, Ctx, Else).

%   output unifications at fresh-variable positions move to the Then branch
split_unifs([], _, _, _, [], []).
split_unifs([V=T|Us], Head, P, CG, UC, UT) :-
    Head =.. [_|Ps],
    (   nth1(I, Ps, X), X == V, nth1(I, P, f), \+ occurs_in(V, CG)
    ->  UC = UC1, UT = [V=T|UT1]
    ;   UC = [V=T|UC1], UT = UT1
    ),
    split_unifs(Us, Head, P, CG, UC1, UT1).

occurs_in(V, T) :- term_variables(T, Vs), var_in(Vs, V).

unif_goals([], true).
unif_goals([U], U) :- !.
unif_goals([U|Us], (U, C)) :- unif_goals(Us, C).

%   the most specific head of a group of clauses (anti-unification)
group_head(Rs, K, Head) :-
    findall(H, member(r(H, _), Rs), [H0|Hs0]),
    copy_term([H0|Hs0], [H1|Hs]),
    foldl(lgg_head, Hs, H1, Head0),
    copy_term(Head0, Head),
    Head =.. [_|As], term_variables(As, HVs),
    term_variables([H0|Hs0], CVs), maplist(var_hint, CVs, Used),
    distinct_names(HVs, Used, [], _), K = K.

lgg_head(H, G0, G) :- lgg(G0, H, G, [], _).

lgg(A, B, G, S0, S) :- A == B, !, G = A, S = S0.
lgg(A, B, G, S0, S) :-
    compound(A), compound(B), functor(A, N, Ar), functor(B, N, Ar), !,
    A =.. [_|As], B =.. [_|Bs],
    lgg_list(As, Bs, Gs, S0, S), G =.. [N|Gs].
lgg(A, B, G, S0, S) :-
    (   member((A1-B1)-V, S0), A1 == A, B1 == B -> G = V, S = S0
    ;   G = V,
        (   var(A), get_attr(A, pl2detlog, Nm) -> fresh(Nm, V)
        ;   var(B), get_attr(B, pl2detlog, Nm) -> fresh(Nm, V)
        ;   true
        ),
        S = [(A-B)-V|S0]
    ).

lgg_list([], [], [], S, S).
lgg_list([A|As], [B|Bs], [G|Gs], S0, S) :- lgg(A, B, G, S0, S1), lgg_list(As, Bs, Gs, S1, S).

name_head_vars(As, _) :- term_variables(As, Vs), numbered_params(Vs, 1).

%   head_match(+Head, +ClauseHead, -Unifs): unify the clause's head with Head; a clause
%   variable at a variable position becomes that variable, anything else is a goal V = T.
head_match(Head, CH, U) :-
    term_variables(Head, HVs),
    hm(Head, CH, HVs, U, []).

hm(V, T, HVs, U0, U) :- var(V), !,
    (   var(T), \+ var_in(HVs, T) -> V = T, U0 = U
    ;   U0 = [V = T|U]
    ).
hm(A, B, HVs, U0, U) :-
    A =.. [_|As], B =.. [_|Bs],
    foldl(hm2(HVs), As, Bs, U0, U).
hm2(HVs, A, B, U0, U) :- hm(A, B, HVs, U0, U).

%   ---- first-answer version (MNN): p__first/N, semideterministic ----
gen_first(K) :-
    first_name(K, FN),
    gen_first(K, FN, first).

gen_first(K, FN, Mode) :-
    resolved(K, Rs), m_pat(K, P),
    ctx(K, Mode, Ctx),
    K = _/A, length(Ps, A), name_params(K, Ps),
    H =.. [FN|Ps],
    Head =.. [x|Ps],
    first_chain(Rs, Head, P, Ctx, Code),
    out(K, Mode, (H :- Code)).

first_chain([], _, _, _, fail).
first_chain([r(CH, Kind)|Rs], Head, P, Ctx, Code) :-
    copy_term(CH-Kind, CH1-Kind1),
    CH1 =.. [_|CA], Head =.. [_|HA], CH2 =.. [x|CA],
    head_match(Head, CH2, U), unif_goals(U, UC),
    term_variables(HA-UC, HV),
    (   Kind1 = commit(G, B)
    ->  append(G, B, Gs), annotate(CH2, Gs, P, As),
        length(G, NG), length(AG, NG), append(AG, AB, As),
        term_variables(HV-B, After),
        tr_first(AG, After, Ctx, CG), tr_first(AB, HV, Ctx, TB),
        conj(UC, CG, Cond),
        (   Rs == [] -> conj(Cond, TB, Code)
        ;   first_chain(Rs, Head, P, Ctx, Else), Code = if_commit(Cond, TB, Else)
        )
    ;   Kind1 = plain(Gs),
        annotate(CH2, Gs, P, As),
        tr_first(As, HV, Ctx, BC), conj(UC, BC, Cond),
        (   Rs == [] -> Code = Cond
        ;   first_chain(Rs, Head, P, Ctx, Else), Code = if_commit(Cond, true, Else)
        )
    ).

%   ---- all-answers version: p__all(Args..., Answers, Tail) ----
gen_all(K) :-
    resolved(K, Rs), m_pat(K, P),
    ctx(K, all, Ctx),
    K = N/A, length(Ps, A), name_params(K, Ps),
    all_name(K, AN), fresh('Out', Out), fresh('T', T),
    append(Ps, [Out, T], HA), H =.. [AN|HA],
    (   form(mnn), all_facts(Rs, Facts)
    ->  G =.. [N|Ps], Code = dl_match(Facts, G, Out, T),
        assertz(note(K, 'MNN facts as data: answers are the facts that unify with the call'))
    ;   all_chain(Rs, N, Ps, P, Out, T, Ctx, Code)
    ),
    out(K, all, (H :- Code)).

all_facts(Rs, Facts) :-
    maplist(fact_of, Rs, Facts).
fact_of(r(H, plain([])), H).

all_chain([], _, _, _, Out, T, _, Out = T).
all_chain([r(CH, Kind)|Rs], N, Ps, P, Out, T, Ctx, Code) :-
    copy_term(CH-Kind, CH1-Kind1),
    arg_copies(Ps, P, Ps1, CopyGs),
    Head =.. [x|Ps1], CH1 =.. [_|CA], CH2 =.. [x|CA],
    head_match(Head, CH2, U), unif_goals(U, UC),
    Ans =.. [N|Ps1],
    term_variables(Ps1-UC, PV),
    (   Kind1 = commit(G, B)
    ->  append(G, B, Gs), annotate(CH2, Gs, P, As),
        length(G, NG), length(AG, NG), append(AG, AB, As),
        term_variables(PV-B, After),
        tr_first(AG, After, Ctx, CG), conj(UC, CG, Cond),
        tr_all(AB, Ans, Out, T, PV, Ctx, Then),
        all_chain(Rs, N, Ps, P, Out, T, Ctx, Else),
        conj(CopyGs, if_commit(Cond, Then, Else), Code)
    ;   Kind1 = plain(Gs),
        annotate(CH2, Gs, P, As),
        (   Rs == [] -> T1 = T ; fresh('T1', T1) ),
        tr_all(As, Ans, Out, T1, PV, Ctx, Body),
        (   UC == true -> C1 = Body ; C1 = if_commit(UC, Body, Out = T1) ),
        (   Rs == [] -> Rest = true ; all_chain(Rs, N, Ps, P, T1, T, Ctx, Rest) ),
        conj(CopyGs, C1, C2), conj(C2, Rest, Code)
    ).

%   each clause works on a copy of the arguments that are not ground
arg_copies(Ps, P, Ps1, Copy) :-
    maplist(arg_copy, Ps, P, Ps1, Pairs),
    exclude(==(none), Pairs, Cs),
    (   Cs == [] -> Copy = true
    ;   pairs_keys_values(Cs, From, To),
        Copy = copy_term(From, To)
    ).

arg_copy(X, g, X, none) :- !.
arg_copy(X, f, Y, none) :- !, copy_hint(X, Y).
arg_copy(X, a, Y, X-Y) :- copy_hint(X, Y).

copy_hint(X, Y) :- ( get_attr(X, pl2detlog, N) -> atom_concat(N, '1', N1), fresh(N1, Y) ; true ).

                 /*******************************
                 *     GOALS IN EACH MODE       *
                 *******************************/

conj(true, X, X) :- !.
conj(X, true, X) :- !.
conj(X, Y, (X, Y)).

%   det: every goal has at most one answer
tr_det([], _, true).
tr_det([A|As], Ctx, Code) :-
    tr_det_goal(A, Ctx, C1), tr_det(As, Ctx, C2), conj(C1, C2, Code).

tr_det_goal(an(b(G), _, _, _, _, _), _, G) :- !.
tr_det_goal(an(u(G), _, _, _, _, _), Ctx, C) :- !, call_det(G, Ctx, C).
tr_det_goal(an(not(S), _, _, _, ID, _), Ctx, if_commit(C, fail, true)) :- !, first_simple(S, ID, Ctx, C).
tr_det_goal(an(once(S), _, _, _, ID, _), Ctx, C) :- !, first_simple(S, ID, Ctx, C).
tr_det_goal(an(ignore(S), _, _, _, ID, _), Ctx, if_commit(C, true, true)) :- !, first_simple(S, ID, Ctx, C).
tr_det_goal(an(findall(T, S, L), _, _, GB, ID, Sh), Ctx, C) :- !, tr_findall(T, S, ID, L, GB-Sh, Ctx, C).
tr_det_goal(an(findall4(T, S, L, T0), _, _, GB, ID, Sh), Ctx, (C, append(L0, T0, L))) :- !,
    fresh('L0', L0), tr_findall(T, S, ID, L0, GB-Sh, Ctx, C).
tr_det_goal(an(aggr(F, E, S, R), _, _, GB, ID, Sh), Ctx, C) :- !, tr_aggr(F, E, S, ID, R, GB-Sh, Ctx, C).
tr_det_goal(an('$cut', _, _, _, _, _), _, true).

%   a deterministic user call: in place, or inlined when it is a one-clause auxiliary
%   predicate whose head arguments are distinct variables
call_det(G, _, C) :-
    key(G, K), aux_of(K, _), \+ table_key(K),
    inline_clause(K, (H :- B)), !,
    copy_term(H-B, H1-B1), H1 = G, C = B1.
call_det(G, _, G) :- key(G, K), need_key(K, det).

inline_clause(K, Cl) :- db_get(inl, K, Cl0), !, Cl = Cl0.
inline_clause(K, Cl) :-
    \+ done(K, det),
    assertz(done(K, det)),
    gen(K, det),
    db_all(out, K-det, Cls),
    partition(main_clause(K), Cls, [(H :- B)], Others),
    H =.. [_|As], is_set_vars(As),
    \+ calls_self(B, H), !,
    retractall(dbv(out, K-det, _, _, _)),
    forall(member(O, Others), db_put(out, K-det, O)),
    Cl = (H :- B),
    db_put(inl, K, Cl),
    assertz(inlined(K)).
inline_clause(K, _) :- need_key(K, det), fail.

main_clause(N/A, (H :- _)) :- functor(H, N, A).

is_set_vars(As) :- maplist(var, As), sort(As, S), length(S, N), length(As, N).

calls_self(B, H) :- functor(H, N, A), sub_term(T, B), callable(T), functor(T, N, A), !.

%   the first answer of one simple goal, bindings kept
first_simple(b(G), true, _, G) :- !.
first_simple(b(G), false, _, dl_once(G)) :- !.
first_simple(u(G), true, Ctx, C) :- !, call_det(G, Ctx, C).
first_simple(u(G), false, _, C) :-
    key(G, K),
    (   kept(K, _)
    ->  C = dl_once(G), need_key(K, prolog)
    ;   first_call(G, C), need_key(K, first)
    ).

kept_or_effect_all(K) :- ( kept(K, _) ; eff_key(K) ), !.

first_call(G, C) :- key(G, K), first_name(K, FN), G =.. [_|As], C =.. [FN|As].
all_call(G, Ans, C) :-
    key(G, K), all_name(K, AN), G =.. [_|As],
    fresh('As', Ans), append(As, [Ans, []], AA), C =.. [AN|AA].

%   findall over a simple goal
tr_findall(T, S, true, L, GB-Sh, Ctx, Code) :- !,
    det_inner(S, Ctx, G),
    term_variables(G-T, GTV), include(var_in(Sh), GTV, Sh1), exclude(var_in(GB), Sh1, NG),
    copy_nonground(NG, G-T, G1-T1, CopyG),
    conj(CopyG, if_commit(G1, L = [T1], L = []), Code).
tr_findall(T, b(G), false, L, _, _, Code) :- !,
    (   bi_effect(G) -> Code = findall(T, G, L)
    ;   fresh('As', As), Code = (dl_all(G, As, []), dl_project(As, G, T, L))
    ).
tr_findall(T, u(G), false, L, _, _, Code) :-
    key(G, K),
    (   kept_or_effect_all(K)
    ->  Code = findall(T, G, L), need_key(K, prolog)
    ;   need_key(K, all), all_call(G, As, AC),
        Code = (AC, dl_project(As, G, T, L))
    ).

det_inner(b(G), _, G).
det_inner(u(G), Ctx, C) :- call_det(G, Ctx, C).

tr_aggr(count, _, S, ID, N, GB-Sh, Ctx, Code) :-
    (   ID == true
    ->  det_inner(S, Ctx, G), term_variables(G, GV), include(var_in(Sh), GV, Sh1),
        exclude(var_in(GB), Sh1, NG),
        copy_nonground(NG, G, G1, CopyG), conj(CopyG, if_commit(G1, N = 1, N = 0), Code)
    ;   S = u(G), key(G, K), \+ kept_or_effect_all(K)
    ->  need_key(K, all), all_call(G, As, AC), Code = (AC, length(As, N))
    ;   S = b(G), \+ bi_effect(G)
    ->  fresh('As', As), Code = (dl_all(G, As, []), length(As, N))
    ;   S = u(G) -> key(G, K), need_key(K, prolog), Code = aggregate_all(count, G, N)
    ;   S = b(G), Code = aggregate_all(count, G, N)
    ).
tr_aggr(F, E, S, ID, R, GS, Ctx, Code) :-
    F \== count,
    fresh('Vs', Vs),
    tr_findall(E, S, ID, Vs, GS, Ctx, C1),
    Code = (C1, dl_aggregate(F, Vs, R)).

%   first: the first answer of a conjunction (semideterministic); Ctx0 are the variables
%   used outside the conjunction
tr_first(As, Ctx0, Ctx, Code) :- tr_first_(As, Ctx0, Ctx, Code).

tr_first_([], _, _, true).
tr_first_([A|As], Out, Ctx, Code) :-
    A = an(G, Det, _, _, _, _),
    term_variables(G, GV), append(GV, Out, Out1),
    (   Det == true
    ->  tr_det_goal(A, Ctx, C1), tr_first_(As, Out1, Ctx, C2), conj(C1, C2, Code)
    ;   As == []
    ->  first_simple(G, false, Ctx, Code)
    ;   form(mnn), all_total(As)
    ->  first_simple(G, false, Ctx, C1), tr_det(As, Ctx, C2), conj(C1, C2, Code)
    ;   form(mnn), G = b(BG), \+ bi_effect(BG), fusable(As, first)
    ->  tr_fused(As, Ctx, Test), Code = dl_fused_first(BG, Test),
        fuse_note(Ctx)
    ;   scan(A, As, Out, Ctx, Code)
    ).

all_det(As) :- forall(member(an(_, D, _, _, _, _), As), D == true).

%   the rest of a conjunction that the runtime can run as one lazy loop: builtins (more
%   generators among them) and deterministic goals; in the all mode they are pure
fusable(As, Mode) :- forall(member(A, As), fusable_goal(A, Mode)).

fusable_goal(an(b(G), _, _, _, _, _), Mode) :- !, ( Mode == all -> \+ bi_effect(G) ; true ).
fusable_goal(an(_, true, _, _, _, _), _).

tr_fused([], _, true).
tr_fused([A|As], Ctx, Code) :-
    (   A = an(b(G), false, _, _, _, _) -> C1 = G ; tr_det_goal(A, Ctx, C1) ),
    tr_fused(As, Ctx, C2), conj(C1, C2, Code).

fuse_note(c(K, _)) :-
    root_of(K, R),
    (   note(R, N), sub_atom(N, 0, _, _, 'MNN fuse') -> true
    ;   assertz(note(R, 'MNN fuse: a builtin generator followed by deterministic goals is enumerated lazily by the runtime (dl_fused_first/2, dl_fused_all/5): the same answers in the same order, and no answer list is built'))
    ).

all_total(As) :- forall(member(an(_, _, T, _, _, _), As), T == true).

%   scan the answers of a nondeterministic goal for the first that the rest accepts
scan(an(G, _, _, _, _, _), As, Out, Ctx, Code) :-
    (   generator(G, Gen, Answers, Pat)
    ->  rest_goals(As, RG),
        term_variables(G-RG, LV),
        shared_vars(LV, Out, Env),
        loop_name(Ctx, s, SN),
        fresh('A', A1), fresh('As', As1),
        H =.. [SN, [A1|As1]|Env], R =.. [SN, As1|Env],
        term_variables(Pat-Env, Out2),
        tr_first_(As, Out2, Ctx, RC),
        conj((A1 = Pat), RC, Cond),
        Ctx = c(K, M),
        out(K, M, (H :- if_commit(Cond, true, R))),
        Call =.. [SN, Answers|Env],
        Code = (Gen, Call)
    ;   tr_island(G, As, Ctx, Code)
    ).

rest_goals(As, Gs) :- maplist(arg(1), As, Gs).

%   a goal with side effects whose answers are needed one by one: an ordinary Prolog
%   conjunction, run by Prolog's own backtracking
tr_island(G, As, Ctx, dl_once((G1, RC))) :-
    island_goal(G, G1),
    tr_first_(As, [], Ctx, RC).

island_goal(b(G), G).
island_goal(u(G), G) :- key(G, K), need_key(K, prolog).

generator(u(G), Gen, Ans, G) :-
    key(G, K), \+ kept_or_effect_all(K), !,
    need_key(K, all), all_call(G, Ans, Gen).
generator(b(G), dl_all(G, Ans, []), Ans, G) :-
    \+ bi_effect(G), fresh('As', Ans).

loop_name(c(K, _), Kind, Name) :-
    root_of(K, R), R = N/_,
    next_count(loop(R), I),
    format(atom(Name), '~w__~w~w', [N, Kind, I]).

%   all: Out-T are the answers Ans of the conjunction, for every way it succeeds
tr_all([], Ans, Out, T, _, _, Out = [Ans|T]).
tr_all([A|As], Ans, Out, T, Seen, Ctx, Code) :-
    A = an(_, true, _, _, _, _), !,
    det_prefix([A|As], Ds, Rest),
    tr_det(Ds, Ctx, DC),
    rest_goals(Ds, DG), term_variables(DG, DV), append(DV, Seen, Seen1),
    tr_all(Rest, Ans, Out, T, Seen1, Ctx, RC),
    (   all_total(Ds) -> conj(DC, RC, Code)
    ;   Code = if_commit(DC, RC, Out = T)
    ).
tr_all([A|As], Ans, Out, T, _, Ctx, Code) :-
    form(mnn), A = an(b(BG), false, _, _, _, _), \+ bi_effect(BG), fusable(As, all), !,
    tr_fused(As, Ctx, Test),
    Code = dl_fused_all(BG, Test, Ans, Out, T),
    fuse_note(Ctx).
tr_all([A|As], Ans, Out, T, Seen, Ctx, Code) :-
    A = an(G, false, _, GB, _, _),
    generator(G, Gen, Answers, Pat), !,
    rest_goals(As, RG),
    term_variables(Pat-RG-Ans, LV),
    shared_vars(LV, Seen, Env0),
    exclude(var_in(GB), Env0, NG),
    loop_name(Ctx, l, LN),
    fresh('A', A1), fresh('As', As1), fresh('Out', LO), fresh('T', LT), fresh('T1', LT1),
    copy_nonground(NG, Pat-As-Ans-Env0, Pat1-As2-Ans1-Env1, CopyG),
    term_variables(Pat1-Env1, Seen2),
    tr_all(As2, Ans1, LO, LT1, Seen2, Ctx, RC),
    append([[A1|As1]|Env0], [LO, LT], HA), LH =.. [LN|HA],
    append([As1|Env0], [LT1, LT], RA), LR =.. [LN|RA],
    append([[]|Env0], [LT, LT], BA), LB =.. [LN|BA],
    conj(CopyG, if_commit(A1 = Pat1, RC, LO = LT1), LBody),
    Ctx = c(K, M),
    out(K, M, LB),
    out(K, M, (LH :- LBody, LR)),
    append([Answers|Env0], [Out, T], CA), Call =.. [LN|CA],
    Code = (Gen, Call).
tr_all([A|_], _, _, _, _, _, _) :-
    A = an(G, _, _, _, _, _),
    throw(unsupported(all_mode_effect(G))).

det_prefix([A|As], [A|Ds], Rest) :- A = an(_, true, _, _, _, _), !, det_prefix(As, Ds, Rest).
det_prefix(As, [], As).

%   rename the variables NG in T (a fresh copy per answer), keeping the others
copy_nonground([], T, T, true) :- !.
copy_nonground(NG, T, T1, copy_term(NG, NG1)) :-
    term_variables(T, TV),
    exclude(var_in(NG), TV, Keep),
    copy_term(Keep-NG-T, Keep1-NG1-T1),
    Keep1 = Keep,
    maplist(rehint, NG, NG1).

rehint(V, V1) :- ( get_attr(V, pl2detlog, N) -> atom_concat(N, '1', N1), put_attr(V1, pl2detlog, N1) ; true ).

                 /*******************************
                 *        ENTRY AND FOLDERS     *
                 *******************************/

%   entry_from_options(+Options, -Goal): the query that the program is run with.
entry_from_options(Options, Goal) :-
    (   option(query(Q), Options) -> parse_goal(Q, Goal)
    ;   option(main(M), Options) -> main_goal(M, Goal)
    ;   init_main(Goal)
    ;   option(purpose(compile), Options), pred_key(main/0, _) -> Goal = main
    ), !,
    add_entry(Goal).

parse_goal(Q, G) :-
    (   ( atom(Q) ; string(Q) )
    ->  term_string(G, Q, [module(pl2detlog_read), variable_names(Vs)]), names_attach(Vs)
    ;   G = Q
    ).

main_goal(M, G) :-
    (   atom(M), pred_key(M/0, _) -> G = M
    ;   atom(M), pred_key(M/1, _) -> G = main_argv(M)
    ;   parse_goal(M, G)
    ).

init_main(G) :-
    src_file(_, P), db_get(item, P, it(_, dir(initialization(G, main), _), _)), !.

add_entry(main_argv(M)) :- !,
    G =.. [M, []], add_entry(G).
add_entry(Goal) :-
    retractall(entry(_, _)),
    assertz(entry(pl2detlog_main, Goal)),
    src_file(0, P),
    db_put(item, P, it(1000000, cl(pl2detlog_main, Goal),
                       ["% the query: pl2detlog_main runs its first answer"])),
    reg_head(pl2detlog_main).

out_root(Form, Options, OutRoot) :-
    (   option(out(D0), Options), option(form(F), Options, both), F \== both
    ->  absolute_file_name(D0, OutRoot)
    ;   option(out(D0), Options)
    ->  absolute_file_name(D0, D), atomic_list_concat([D, Form], '/', OutRoot)
    ;   root_dir(Root), src_file(0, P),
        file_base_name(P, B), file_name_extension(Base, _, B),
        format(atom(OutRoot), '~w/~w_~w', [Root, Base, Form])
    ).

rel_path(P, Rel) :-
    root_dir(Root),
    ( Root == '/' -> R1 = '' ; R1 = Root ),
    atom_concat(R1, Rest, P), atom_concat('/', Rel, Rest), !.
rel_path(P, Rel) :- file_base_name(P, Rel).

root_out_file(OutRoot, Main) :-
    src_file(0, P), rel_path(P, Rel),
    atomic_list_concat([OutRoot, Rel], '/', Main).

                 /*******************************
                 *            WRITING           *
                 *******************************/

write_program(Form, OutRoot) :-
    make_dirs(OutRoot),
    nb_setval(pl2detlog_out_root, OutRoot),
    retractall(dbv(written, _, _, _, _)),
    module_property(pl2detlog, file(Self)),
    file_directory_name(Self, SelfDir),
    atomic_list_concat([SelfDir, 'detlog_rt.pl'], '/', RtSrc),
    atomic_list_concat([OutRoot, 'detlog_rt.pl'], '/', Rt),
    copy_text_file(RtSrc, Rt),
    forall(src_file(_, P), write_file(Form, P, OutRoot, Rt)),
    write_proofs(Form, OutRoot).

write_file(Form, P, OutRoot, Rt) :-
    rel_path(P, Rel),
    atomic_list_concat([OutRoot, Rel], '/', OP),
    file_directory_name(OP, OD), make_dirs(OD),
    relative_to(Rt, OP, RtRel0),
    file_name_extension(RtRel, _, RtRel0),
    db_all(item, P, Items0),
    sort(1, @=<, Items0, Items),
    setup_call_cleanup(
        open(OP, write, S),
        ( form_title(Form, Title),
          format(S, "% ~w of ~w, written by pl2detlog.~n", [Title, Rel]),
          (   Items = [it(_, dir(module(_, _), _), _)|_]
          ->  true
          ;   format(S, ":- use_module(~q).~n~n", [RtRel])
          ),
          write_items(Items, S, P, RtRel)
        ),
        close(S)).

form_title(detlog, 'Detlog').
form_title(mnn, 'Detlog MNN').

write_items([], _, _, _).
write_items([it(_, Item, Cmts)|Is], S, P, RtRel) :-
    write_comments(S, Cmts),
    write_item(Item, S, P, RtRel),
    write_items(Is, S, P, RtRel).

write_comments(_, []) :- !.
write_comments(S, Cs) :- forall(member(C, Cs), format(S, "~s~n", [C])).

write_item(eof, _, _, _).
write_item(dir(D, Loads), S, _, RtRel) :-
    rewrite_directive(D, Loads, D1),
    print_clause(S, (:- D1)),
    (   D = module(_, _) -> format(S, ":- use_module(~q).~n", [RtRel]) ; true ).
write_item(cl(H, _), S, P, _) :-
    key(H, K),
    (   first_clause_here(K, P, H) -> emit_block(S, K) ; true ).

first_clause_here(K, P, _) :-
    \+ dbv(written, K, _, _, _),
    src_file(_, P1),
    dbv(item, P1, it(_, cl(H1, _), _), _, _), key(H1, K), !,
    P1 == P,
    assertz(dbv(written, K, x, [], [])).

rewrite_directive(D, Loads, D1) :-
    load_directive(D, _), Loads \== [], !,
    D =.. [F, Spec|R], map_spec(Spec, Loads, Spec1), D1 =.. [F, Spec1|R].
rewrite_directive([H|T], Loads, L1) :- Loads \== [], !,
    maplist(map_one(Loads), [H|T], L1).
rewrite_directive(module(M, Ex), _, module(M, Ex2)) :- !,
    findall(PI, ( member(K, Ex), K = _/_, export_version(K, PI) ), New),
    append(Ex, New, Ex1), list_to_set(Ex1, Ex2).
rewrite_directive(initialization(G, main), _, initialization(N, main)) :-
    entry(N, G0), G0 =@= G, !.
rewrite_directive(initialization(G), _, initialization(N)) :-
    entry(N, G0), G0 =@= G, !.
rewrite_directive(D, _, D).

%   the converted versions of an exported predicate are exported too
export_version(N/A, FN/A) :- dbv(out, (N/A)-first, _, _, _), first_name(N/A, FN).
export_version(N/A, AN/A2) :- dbv(out, (N/A)-all, _, _, _), all_name(N/A, AN), A2 is A + 2.

map_spec(L, Loads, L1) :- is_list(L), !, maplist(map_one(Loads), L, L1).
map_spec(S, Loads, S1) :- map_one(Loads, S, S1).

%   relative paths stay as they are (the folder structure is the same); an absolute path
%   to a program file is moved into the new folder
map_one(Loads, F, F1) :-
    member(F0-Abs, Loads), F0 == F, is_absolute_file_name(F), current_out_root(OR), !,
    rel_path(Abs, Rel), atomic_list_concat([OR, Rel], '/', F1).
map_one(_, F, F).

current_out_root(OR) :- nb_current(pl2detlog_out_root, OR), OR \== [].

%   a predicate's block: its versions, then its auxiliary predicates
emit_block(S, K) :-
    block_note(S, K),
    emit_versions(S, K),
    forall(aux_of(A, K), emit_aux(S, A)).

emit_aux(S, A) :-
    emit_versions(S, A),
    forall(aux_of(A2, A), emit_aux(S, A2)).

emit_versions(S, K) :-
    forall(member(M, [det, first, all, entry, prolog, dead]),
           (   db_all(out, K-M, Cls), Cls \== []
           ->  partition(is_main(K, M), Cls, Main, Loops),
               forall(member(C, Main), print_clause(S, C)),
               forall(member(C, Loops), print_clause(S, C)),
               nl(S)
           ;   true
           )).

is_main(K, M, C) :- ( C = (:- _) -> true ; C = (H :- _) -> true ; H = C ), version_head(K, M, H).

version_head(N/A, M, H) :- callable(H),
    (   memberchk(M, [det, prolog, dead, entry]) -> functor(H, N, A)
    ;   M == first -> first_name(N/A, FN), functor(H, FN, A)
    ;   M == all -> all_name(N/A, AN), A2 is A + 2, functor(H, AN, A2)
    ).
version_head(_, _, (:- _)).

block_note(S, K) :-
    (   kept(K, Why) -> format(S, "% ~q: kept as Prolog (~w)~n", [K, Why])
    ;   dbv(out, K-dead, _, _, _) -> format(S, "% ~q: not used by the query; as written~n", [K])
    ;   true
    ),
    forall(note(K, N), format(S, "% ~w~n", [N])).

%   file helpers (core SWI-Prolog only)
make_dirs(D) :- exists_directory(D), !.
make_dirs(D) :-
    file_directory_name(D, P),
    ( P \== D -> make_dirs(P) ; true ),
    ( exists_directory(D) -> true ; make_directory(D) ).

copy_text_file(From, To) :-
    read_file_to_string(From, S, []),
    setup_call_cleanup(open(To, write, Out), write(Out, S), close(Out)).

%   relative_to(+Target, +FromFile, -Rel): Target's path relative to FromFile's folder
relative_to(Target, From, Rel) :-
    file_directory_name(From, FD),
    atomic_list_concat(TP, '/', Target), atomic_list_concat(FP, '/', FD),
    common_prefix(TP, FP, C), length(C, N),
    length(TC, N), append(TC, TRest, TP), length(FC, N), append(FC, FRest, FP),
    exclude(==(''), FRest, FR),
    length(FR, Up), length(Ups, Up), maplist(=('..'), Ups),
    append(Ups, TRest, RP),
    (   RP = ['..'|_] -> atomic_list_concat(RP, '/', Rel)
    ;   atomic_list_concat(['.'|RP], '/', Rel)
    ).

                 /*******************************
                 *           PRINTING           *
                 *******************************/

print_clause(S, Cl0) :-
    copy_term(Cl0, Cl),
    bind_names(Cl),
    (   Cl = (:- D)
    ->  format(S, ":- ", []), pflat(S, D, 1199), format(S, ".~n", [])
    ;   Cl = (H :- B), B \== true
    ->  pflat(S, H), format(S, " :-~n", []),
        conj_list(B, Gs),
        pgoals(Gs, S, 4),
        format(S, ".~n", [])
    ;   ( Cl = (H :- true) -> true ; H = Cl ),
        pflat(S, H), format(S, ".~n", [])
    ).

pgoals([G], S, Col) :- !, tab(S, Col), pgoal(S, G, Col).
pgoals([G|Gs], S, Col) :- tab(S, Col), pgoal(S, G, Col), format(S, ",~n", []), pgoals(Gs, S, Col).

wopts([quoted(true), numbervars(true), spacing(next_argument), portray(false),
       module(pl2detlog_read), priority(999)]).

pflat(S, T) :- wopts(O), write_term(S, T, O).
pflat(S, T, Pri) :- wopts(O0), select(priority(_), O0, O1), write_term(S, T, [priority(Pri)|O1]).
flat(T, A) :- with_output_to(string(A), pflat(current_output, T)).
flat(T, Pri, A) :- with_output_to(string(A), pflat(current_output, T, Pri)).

pgoal(S, G, Col) :-
    ( G = (_;_) ; G = (_->_) ; G = (_*->_) ), !,
    disj_alts(G, Alts),
    write(S, '(   '), C4 is Col + 4,
    palts(Alts, S, Col, C4),
    nl(S), tab(S, Col), write(S, ')').
pgoal(S, G, Col) :-
    flat(G, F), string_length(F, L),
    (   Col + L =< 92
    ->  write(S, F)
    ;   G = if_commit(C, T, E)
    ->  C1 is Col + 10,
        write(S, 'if_commit('), parg(S, C, C1), format(S, ",~n", []),
        tab(S, C1), parg(S, T, C1), format(S, ",~n", []),
        tab(S, C1), parg(S, E, C1), write(S, ')')
    ;   G = dl_once(X), X = (_, _)
    ->  C1 is Col + 8, write(S, 'dl_once('), parg(S, X, C1), write(S, ')')
    ;   write(S, F)
    ).

parg(S, X, Col) :-
    (   X = (_, _), flat(X, F), string_length(F, L), Col + L > 92
    ->  conj_list(X, Gs), C2 is Col + 2,
        write(S, '( '), pconj(Gs, S, C2), format(S, "~n", []), tab(S, Col), write(S, ')')
    ;   X = (_, _)
    ->  flat(X, 1000, F), format(S, "( ~w )", [F])
    ;   pgoal(S, X, Col)
    ).

disj_alts((A;B), [A|Bs]) :- !, disj_alts(B, Bs).
disj_alts(A, [A]).

palts([A], S, Col, C4) :- !, palt(A, S, Col, C4).
palts([A|As], S, Col, C4) :-
    palt(A, S, Col, C4), nl(S), tab(S, Col), write(S, ';   '), palts(As, S, Col, C4).

palt((C->T), S, Col, C4) :- !,
    conj_list(C, Cs), pconj(Cs, S, C4), nl(S), tab(S, Col), write(S, '->  '),
    conj_list(T, Ts), pconj(Ts, S, C4).
palt((C*->T), S, Col, C4) :- !,
    conj_list(C, Cs), pconj(Cs, S, C4), nl(S), tab(S, Col), write(S, '*-> '),
    conj_list(T, Ts), pconj(Ts, S, C4).
palt(G, S, _, C4) :- conj_list(G, Gs), pconj(Gs, S, C4).

pconj([], S, _) :- !, write(S, true).
pconj([G], S, Col) :- !, pgoal(S, G, Col).
pconj([G|Gs], S, Col) :- pgoal(S, G, Col), format(S, ",~n", []), tab(S, Col), pconj(Gs, S, Col).

%   give every variable a name: its source name, a hint, or '_' when it occurs once
bind_names(T) :-
    term_variables_list(T, All),
    term_variables(T, Vs),
    foldl(bind_name(All), Vs, [], _).

bind_name(All, V, Used, [Name|Used]) :-
    include(==(V), All, Os), length(Os, N),
    (   N =:= 1 -> Name = '_'
    ;   ( get_attr(V, pl2detlog, H0) -> var_name(H0, H) ; H = 'V' ),
        unique_name(H, Used, Name)
    ),
    del_attr(V, pl2detlog),
    V = '$VAR'(Name).

var_name(H0, H) :-
    atom_codes(H0, [C|Cs]),
    (   ( code_type(C, upper) ; C == 0'_ ) -> H = H0
    ;   code_type(C, to_lower(U)), atom_codes(H, [U|Cs])
    ).
var_name('_', 'V') :- !.

unique_name(H, Used, Name) :-
    (   H \== '_', \+ memberchk(H, Used) -> Name = H
    ;   between(1, inf, I), format(atom(Name), '~w~w', [H, I]), \+ memberchk(Name, Used) -> true
    ).

                 /*******************************
                 *            PROOFS            *
                 *******************************/

write_proofs(Form, OutRoot) :-
    atomic_list_concat([OutRoot, 'PROOFS.txt'], '/', F),
    src_file(0, P), rel_path(P, Rel),
    form_title(Form, Title),
    setup_call_cleanup(open(F, write, S), proof_report(S, Title, Rel), close(S)).

proof_report(S, Title, Rel) :-
    format(S, "~w of ~w: the rewrites and their side conditions~n~n", [Title, Rel]),
    format(S, "Each rule below was checked on the program; the compile step also runs the query~n", []),
    format(S, "in every form and checks the output is Prolog's before timing it.~n~n", []),
    forall(( pred_key(K, _), \+ aux_of(K, _) ), pred_proof(S, K)).

pred_proof(S, K) :-
    findall(L, proof_line(K, L), Ls),
    (   Ls == [] -> true
    ;   format(S, "~q~n", [K]), forall(member(L, Ls), format(S, "  - ~w~n", [L])), nl(S)
    ).

proof_line(K, L) :- note(K, L).
proof_line(K, L) :- kept(K, Why), format(atom(L), 'kept as Prolog: ~w', [Why]).
proof_line(K, L) :-
    conv_key(K), m_pat(K, P), P \== none,
    ncls(K, Cls), resolved(K, Rs),
    nth1(I, Cls, cl(_, commit(_, _))), nth1(I, Rs, r(_, Kind)),
    (   Kind = plain(_)
    ->  format(atom(L), 'CUT clause ~w: removed; its guard is deterministic and no later clause matches a call ~w that it matches', [I, P])
    ;   format(atom(L), 'CUT clause ~w: necessary; written as if_commit/3', [I])
    ).
proof_line(K, L) :-
    det_key(K), m_pat(K, P),
    format(atom(L), 'DET: called as ~w, the clauses exclude each other and every goal has at most one answer', [P]).
proof_line(K, L) :-
    conv_key(K), \+ det_key(K), \+ kept(K, _), m_pat(K, P), P \== none,
    all_name(K, AN),
    (   eff_key(K)
    ->  format(atom(L), 'nondeterministic with side effects (called as ~w): first answers in Detlog, answer lists never built', [P])
    ;   format(atom(L), 'ALL: nondeterministic (called as ~w); ~w returns the answers in Prolog order', [P, AN])
    ).

                 /*******************************
                 *     COMPILE: TIME, PICK, BUILD    *
                 *******************************/

bench_form(Goal, Budget, Form-Dir-Main, r(Form, Dir, Main, Res, Time)) :-
    (   Form == prolog -> goal_text(Goal, GT) ; GT = "pl2detlog_main" ),
    tmp_file(pl2detlog, Base),
    atom_concat(Base, '_driver.pl', Driver),
    atom_concat(Base, '_result.pl', Result),
    module_property(pl2detlog, file(Self)), file_directory_name(Self, SD),
    atomic_list_concat([SD, 'pl2detlog_bench'], '/', BM),
    setup_call_cleanup(open(Driver, write, S),
                       ( portray_clause(S, (:- use_module(BM))),
                         portray_clause(S, (pl2detlog_bench_run :-
                                               pl2detlog_bench:bench(Main, GT, Result, Budget))) ),
                       close(S)),
    current_prolog_flag(executable, Exe),
    shell_quote(Exe, QE), shell_quote(Driver, QD),
    format(string(Cmd), "~w -q -g pl2detlog_bench_run -t halt ~w < /dev/null > /dev/null 2>&1",
           [QE, QD]),
    shell(Cmd, _),
    (   exists_file(Result),
        catch(setup_call_cleanup(open(Result, read, RS), read_term(RS, T, []), close(RS)),
              _, fail),
        T = result(R, Out, _, Time0)
    ->  Res = R-Out, Time = Time0
    ;   Res = error(no_result)-"", Time = inf
    ),
    ( getenv('PL2DETLOG_KEEP', _) -> format(user_error, "driver ~w~n", [Driver]) ; catch(delete_file(Driver), _, true) ),
    catch(delete_file(Result), _, true).

goal_text(G, T) :-
    with_output_to(string(T), write_term(G, [quoted(true), module(pl2detlog_read)])).

shell_quote(A, Q) :-
    atomic_list_concat(Parts, '\'', A),
    atomic_list_concat(Parts, '\'\\\'\'', A1),
    atomic_list_concat(['\'', A1, '\''], Q).

report_results(Rs, Best) :-
    (   memberchk(r(prolog, _, _, Ref, _), Rs) -> true ; Rs = [r(_, _, _, Ref, _)|_] ),
    format(user_error, "~n% ~w~t~12|~w~t~30|~w~n", [form, 'time per run', 'output']),
    forall(member(r(F, _, _, R, T), Rs),
           ( ( R == Ref -> Same = 'same as Prolog' ; R = error(E)-_ -> format(atom(Same), 'error: ~q', [E]) ; Same = 'DIFFERS: not used' ),
             time_text(T, TT),
             format(user_error, "% ~w~t~12|~w~t~30|~w~n", [F, TT, Same]) )),
    include(same_as(Ref), Rs, Ok),
    (   Ok == [] -> Rs = [Best|_]
    ;   foldl(faster, Ok, none, Best)
    ),
    Best = r(BF, _, _, _, _),
    format(user_error, "% fastest: ~w~n~n", [BF]).

same_as(Ref, r(_, _, _, R, T)) :- R == Ref, T \== inf.

faster(R, none, R) :- !.
faster(R, B, Best) :-
    R = r(_, _, _, _, T1), B = r(_, _, _, _, T2),
    ( T1 < T2 -> Best = R ; Best = B ).

time_text(inf, '-') :- !.
time_text(T, A) :-
    Us is T * 1000000,
    (   Us >= 1000 -> Ms is Us / 1000, format(atom(A), '~3f ms', [Ms])
    ;   format(atom(A), '~2f us', [Us])
    ).

build_exe(Form, _Dir, Main, Exe) :-
    current_prolog_flag(executable, SW),
    (   init_main(_) -> GoalOpt = ''
    ;   Form == prolog -> entry(_, G), goal_text(G, GT), shell_quote(GT, QG),
        format(atom(GoalOpt), '--goal=~w', [QG])
    ;   GoalOpt = '--goal=pl2detlog_main'
    ),
    file_directory_name(Main, MD),
    maplist(shell_quote, [SW, Exe, Main, MD], [QS, QX, QM, QD]),
    format(string(Cmd), "cd ~w && ~w -o ~w ~w --toplevel=halt --stand_alone=true -c ~w > /dev/null 2>&1",
           [QD, QS, QX, GoalOpt, QM]),
    shell(Cmd, St),
    (   St =:= 0 -> true ; throw(error(pl2detlog(build_failed(Cmd)), _)) ).

                 /*******************************
                 *         COMMAND LINE         *
                 *******************************/

pl2detlog_cli([convert, File|Args]) :- !,
    cli_opts(Args, Opts),
    pl2detlog_convert(File, Opts).
pl2detlog_cli([compile, File|Args]) :- !,
    cli_opts(Args, Opts),
    pl2detlog_compile(File, [purpose(compile)|Opts]).
pl2detlog_cli(_) :-
    format(user_error, "~s", [
"usage: swipl pl2detlog convert FILE [-g MAIN | -q QUERY] [--form detlog|mnn|both] [--out DIR]
       swipl pl2detlog compile FILE [-g MAIN | -q QUERY] [-o EXE] [--forms prolog,detlog,mnn]
                                    [--budget SECONDS]
"]).

cli_opts([], []).
cli_opts([O, V|As], [Opt|Os]) :- cli_opt(O, V, Opt), !, cli_opts(As, Os).
cli_opts([A|_], _) :- throw(error(pl2detlog(unknown_option(A)), _)).

cli_opt('-g', V, main(V)).
cli_opt('--main', V, main(V)).
cli_opt('-q', V, query(V)).
cli_opt('--query', V, query(V)).
cli_opt('--form', V, form(F)) :- atom_string(F, V).
cli_opt('--out', V, out(V)).
cli_opt('-o', V, exe(V)).
cli_opt('--forms', V, forms(Fs)) :- atomic_list_concat(Fs, ',', V).
cli_opt('--budget', V, budget(B)) :- atom_number(V, B).

:- multifile prolog:message//1.
prolog:message(error(pl2detlog(no_main), _)) -->
    [ 'pl2detlog: name the main predicate (-g main) or give a query (-q "Goal"): the program has no main/0 and no initialization(main, main)' ].
