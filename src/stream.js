/* pl2detlog stream code: Detlog without answer packets.

   P.toStreams(conv) turns a conversion's normalised, cut-free program (conv.ir) into Detlog in which
   every predicate p/N is an answer stream p__k(A1, ..., AN, K):

   - it passes each answer, in Prolog's order, to the continuation K and succeeds, keeping the bindings,
     at the first answer that K accepts;
   - a rejected answer is undone by if_commit/3 (the engine's trail), so no answer list is built and no
     environment is copied;
   - the rest of a conjunction after a call is a continuation term p__cN(Vars..., K) carrying the
     caller's own variables; its clause of dl_k/1 runs the rest.  dl_k/1's clauses are told apart by
     their first argument, so there is no call/N and no choicepoint;
   - builtin generators (member/2, between/3, select/3, nth0/3, nth1/3) are Detlog loops of the stream
     library below; any other nondeterministic builtin is read through builtin_rows/2;
   - findall/3, findall/4 and aggregate_all/3 collect answers into a bag (dl_bag_new/1, dl_collect/2,
     dl_bag_list/2): that list is the program's own result;
   - a cut inside ; or -> commits through a cut cell (dl_cut_new/1, dl_cut_set/1, dl_cut_off/1):
     after the cut, every earlier alternative of the clause and every later clause stops.

   The query '$queryN'(Vars) keeps its packet entry '$queryN__cp'(Vars, Rows): it collects the answers
   and the text written before each one (dl_query_new/1, dl_bag_row/2, dl_bag_rows/2), so every consumer
   of query packets is unchanged.  In SWI-Prolog these come from src/detlog_stream_rt.pl.
   This is the only place answers are collected for a caller. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, list, deref, listToArray, termVars, show } = P;
  const D = deref;
  const TRUE = Atom('true');
  const isTrue = t => { t = D(t); return t.t === 'a' && t.n === 'true'; };
  const conj = gs => { gs = gs.filter(g => !isTrue(g)); if (!gs.length) return TRUE; let r = gs[gs.length - 1]; for (let i = gs.length - 2; i >= 0; i--) r = Cmp(',', [gs[i], r]); return r; };
  const flat = (g, out) => { out = out || []; g = D(g); if (g.t === 'c' && g.f === ',' && g.a.length === 2) { flat(g.a[0], out); flat(g.a[1], out); } else if (!isTrue(g)) out.push(g); return out; };
  const kk = g => P.key(g);
  const isC = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; };
  const LIB_GEN = { 'member/2': g => Cmp('dl_member_k', [g.a[1], g.a[0]]), 'between/3': g => Cmp('dl_between_k', [g.a[0], g.a[1], g.a[2]]),
    'select/3': g => Cmp('dl_select_k', [g.a[1], g.a[0], g.a[2]]), 'nth0/3': g => Cmp('dl_nth_k', [g.a[1], Int(0), g.a[0], g.a[2]]),
    'nth1/3': g => Cmp('dl_nth_k', [g.a[1], Int(1), g.a[0], g.a[2]]) };

  // the stream library, in Detlog
  const LIB = `% ---- stream library: lazy generators, continuations, collection ----
dl_k(true).
dl_k(dl_collect(B, T)) :- dl_bag_add(B, T), fail.
dl_k(dl_row(B, Vs)) :- dl_bag_row(B, Vs), fail.
dl_k(dl_rowmax(B, Vs, N)) :- dl_bag_row(B, Vs), dl_bag_count(B, C), C >= N.
dl_k(dl_rowk(Rs, Pat, K)) :- dl_rows_k(Rs, Pat, K).
dl_member_k(L, X, K) :- L = [Y|Ys], if_commit(Ys == [], (X = Y, dl_k(K)), if_commit((X = Y, dl_k(K)), true, dl_member_k(Ys, X, K))).
dl_between_k(I, H, X, K) :- dl_between_ok(I, H), if_commit((X = I, dl_k(K)), true, (I1 is I + 1, dl_between_k(I1, H, X, K))).
dl_between_ok(I, H) :- if_commit(H == inf, true, if_commit(H == infinite, true, I =< H)).
dl_select_k(L, X, R, K) :- L = [H|T], if_commit((X = H, R = T, dl_k(K)), true, (R = [H|R1], dl_select_k(T, X, R1, K))).
dl_nth_k(L, I0, I, E, K) :- L = [X|Xs], if_commit((I = I0, E = X, dl_k(K)), true, (I1 is I0 + 1, dl_nth_k(Xs, I1, I, E, K))).
dl_rows_k(Rs, Pat, K) :- Rs = [R|Rs1], dl_row_k(R, Rs1, Pat, K).
dl_row_k(e(Row), Rs, Pat, K) :- if_commit((Row = Pat, dl_k(K)), true, dl_rows_k(Rs, Pat, K)).
dl_facts_k(Fs, Pat, K) :- Fs = [F|Fs1], if_commit((copy_term(F, F1), F1 = Pat, dl_k(K)), true, dl_facts_k(Fs1, Pat, K)).
`;

  // deterministic builtins without side effects (a query of these and DET calls has a status form)
  const PURE = new Set(['is/2', '=/2', '==/2', '\\==/2', '</2', '>/2', '=</2', '>=/2', '=:=/2', '=\\=/2', 'numlist/3', 'true/0',
    'atom/1', 'number/1', 'integer/1', 'var/1', 'nonvar/1', 'is_list/1', 'atom_length/2', 'msort/2', 'sort/2', 'reverse/2', 'sum_list/2', 'max_list/2', 'min_list/2']);
  function toStreams(conv, opts) {
    opts = opts || {};
    const ir = conv.ir;
    const clauses = []; // [term]
    const user = new Set(ir.keys());
    // every clause carries its rule (src/proof.js checks them): RULE is the rule of the code being built
    const tags = []; let RULE = 'k_clause', PRED = '';
    const emit = (t, rule) => { clauses.push(t); tags.push({ rule: rule || RULE, pred: PRED }); };
    const kname = f => f + '__k';
    let contN = 0, varN = 0; const pwDone = new Set();
    const V = p => Var(p + '__' + (++varN));

    // MNN: which predicates the conversion made DET, MEMO or S2A, and their packet-free code to reuse
    const kindOf = new Map((conv.genPreds || []).map(g => [g.key, g.kind]));
    const convCl = conv.clauses || [];
    const headName = t => { t = D(t); const h = isC(t, ':-', 2) ? D(t.a[0]) : t; return h.t === 'c' ? h.f : h.t === 'a' ? h.n : ''; };
    const detCode = new Map(); // p/n -> [clause terms of p__d...]
    const s2aCode = new Map(); // p/n -> s2a_rows(Spec, Args, R) goal
    for (const c of convCl) {
      const nm = headName(c.term), pk = c.pred; if (!pk) continue;
      const f0 = pk.slice(0, pk.lastIndexOf('/'));
      if (nm.startsWith(f0 + '__d') && nm !== f0 + '__dr') { if (!detCode.has(pk)) detCode.set(pk, []); detCode.get(pk).push(c.term); }
      if (kindOf.get(pk) === 's2a' && isC(c.term, ':-', 2) && isC(c.term.a[1], 's2a_rows', 3)) s2aCode.set(pk, D(c.term.a[1]));
    }
    const prog = conv.prog;

    for (const [k, rec] of ir) {
      const i = k.lastIndexOf('/'); const f = k.slice(0, i), n = +k.slice(i + 1);
      const A = []; for (let j = 0; j < n; j++) A.push(Var('A__' + (j + 1)));
      const KV = Var('K__0');
      const head = Cmp(kname(f), A.concat([KV]));
      PRED = k; RULE = 'k_clause';
      if (rec.error) { emit(Cmp(':-', [head, Cmp('detlog_unsupported', [Cmp('/', [Atom(f), Int(n)]), Str(rec.error)])])); continue; }
      const cls = rec.clauses;
      if (!cls.length) { emit(Cmp(':-', [head, P.FAIL])); continue; }
      // MNN S2A: the predicate's rows, walked lazily
      if (s2aCode.has(k)) {
        const g = s2aCode.get(k), Rs = V('Rs');
        emit(Cmp(':-', [head, conj([Cmp('s2a_rows', [g.a[0], list(A), Rs]), Cmp('dl_rows_k', [Rs, list(A), KV])])]), 'k_s2a');
        continue;
      }
      const isDet = detCode.has(k), isMemo = kindOf.get(k) === 'memo';
      const base = isDet || isMemo ? f + '__kc' : f + '__k';
      const memoName = isDet ? f + '__km' : f + '__k';
      const top = isMemo ? memoName : base;
      if (isMemo) {
        // MEMO: the answers of a pure predicate per call variant, from the table
        const F = V('F'), Rs = V('Rs'), Bg = V('B');
        RULE = 'k_memo';
        emit(Cmp(':-', [Cmp(memoName, A.concat([KV])), conj([Cmp('memo_lookup', [Cmp('/', [Atom(f), Int(n)]), list(A), F]), Cmp(f + '__kmemo', [F].concat(A, [KV]))])]));
        const A2 = A.map((_, j) => V('A')), K2 = V('K'), R2 = V('R');
        emit(Cmp(':-', [Cmp(f + '__kmemo', [Cmp('found', [R2])].concat(A2, [K2])), Cmp('dl_rows_k', [R2, list(A2), K2])]));
        const A3 = A.map(() => V('A')), K3 = V('K'), R3 = V('R'), B3 = V('B');
        emit(Cmp(':-', [Cmp(f + '__kmemo', [Atom('none')].concat(A3, [K3])), conj([Cmp('dl_bag_new', [B3]),
          Cmp('if_commit', [Cmp(base, A3.concat([Cmp('dl_collect', [B3, Cmp('e', [list(A3)])])])), TRUE, TRUE]),
          Cmp('dl_bag_list', [B3, R3]), Cmp('memo_store', [Cmp('/', [Atom(f), Int(n)]), list(A3), R3]), Cmp('dl_rows_k', [R3, list(A3), K3])])]));
        void F; void Rs; void Bg;
      }
      if (isDet) {
        // DET: the deterministic-mode status code; maybe (several clauses possible) runs the stream
        RULE = 'k_det';
        for (const t of detCode.get(k)) emit(t);
        const S = V('S');
        emit(Cmp(':-', [head, Cmp('if_commit', [conj([Cmp(f + '__d', A.concat([S])), Cmp('\\==', [S, Atom('maybe')])]),
          conj([Cmp('==', [S, Atom('yes')]), Cmp('dl_k', [KV])]), Cmp(top, A.concat([KV]))])]));
        if (isMemo) { const Pk = V('P'), Bp = V('B');
          emit(Cmp(':-', [Cmp(f + '__cp', A.concat([Pk])), conj([Cmp('dl_bag_new', [Bp]),
            Cmp('if_commit', [Cmp(memoName, A.concat([Cmp('dl_collect', [Bp, Cmp('e', [list(A)])])])), TRUE, TRUE]), Cmp('dl_bag_list', [Bp, Pk])])]), 'k_memo'); }
      }
      // facts: a table walked by the stream library
      if (cls.length > 1 && cls.every(c => isTrue(c.body))) {
        const rows = cls.map(c => list(D(c.head).t === 'c' ? D(c.head).a : []));
        emit(Cmp(':-', [head, Cmp('dl_facts_k', [list(rows), list(A), KV])]), 'k_facts');
        continue;
      }
      RULE = 'k_clause';
      const cut = cls.some(c => hasCut(c.body));
      const C = Var('C__0');
      const clauseGoal = (c, j) => {
        const m = new Map(); const t = P.copy(Cmp(':-', [c.head, c.body]), m);
        const h = D(t.a[0]); const hargs = h.t === 'c' ? h.a : [];
        const K1 = V('K'), C1 = cut ? V('C') : null;
        const ctx = { f, cut: C1, outer: termVars(Cmp('h', hargs.concat([K1]))) };
        const body = genConj(flat(t.a[1]), K1, ctx);
        const cname = cls.length === 1 && !cut ? base : base + (j + 1);
        emit(Cmp(':-', [Cmp(cname, hargs.concat(C1 ? [C1, K1] : [K1])), conj(body)]));
        return Cmp(cname, A.concat(cut ? [C, KV] : [KV]));
      };
      if (cls.length === 1 && !cut) { clauseGoal(cls[0], 0); continue; }
      const calls = cls.map(clauseGoal);
      let chain = calls[calls.length - 1];
      for (let j = calls.length - 2; j >= 0; j--) chain = Cmp('if_commit', [calls[j], TRUE, cut ? conj([Cmp('dl_cut_off', [C]), chain]) : chain]);
      // first-argument indexing: clauses told apart by their first argument (a different principal functor,
      // or an arithmetic guard that excludes the others' numbers) are dispatched, not tried in turn, when the
      // argument is bound.  The clause that runs is then a tail call, so its answers do not leave a pending
      // alternative on the stack (fib(0, 0), fib(1, 1), fib(N, F) :- N > 1, ...).
      const ix = !cut && n > 0 ? indexTests(cls, A[0]) : null;
      if (ix) {
        let d = P.FAIL;
        for (let j = calls.length - 1; j >= 0; j--) d = Cmp('if_commit', [ix[j], calls[j], d]);
        emit(Cmp(':-', [Cmp(base, A.concat([KV])), Cmp('if_commit', [Cmp('nonvar', [A[0]]), d, chain])]), 'k_index');
        continue;
      }
      emit(Cmp(':-', [Cmp(base, A.concat([KV])), cut ? conj([Cmp('dl_cut_new', [C]), chain]) : chain]), 'k_pred');
    }

    // queries: the packet entry, collecting answers and the text written before each
    for (const q of conv.queries || []) {
      PRED = q.pred + '/' + q.vars.length; RULE = 'k_query';
      const vs = q.vars.map(v => Var(v));
      const B = V('B'), R = V('R');
      const streamed = Cmp('if_commit', [Cmp(kname(q.pred), vs.concat([Cmp('dl_row', [B, list(vs)])])), TRUE, TRUE]);
      // MNN: a query whose goals are DET calls and pure builtins first tries its deterministic-mode status:
      // yes is the one answer, in place (no row copy); no is none; maybe runs the stream from the start
      // MNN: a query that is one call of an S2A predicate takes its rows from the table: they are the packet
      const qs = queryS2A(q, vs);
      if (qs) {
        const same = qs.args.length === vs.length && qs.args.every((x, i) => D(x) === vs[i]);
        const Rs = V('Rs');
        emit(Cmp(':-', [Cmp(q.pred + '__cp', vs.concat([R])), same ? Cmp('s2a_rows', [qs.spec, list(vs), R])
          : conj([Cmp('s2a_rows', [qs.spec, list(qs.args), Rs]), Cmp('splice_extend', [Rs, list(qs.args), Cmp('e', [list(vs)]), R])])]));
        continue;
      }
      const qd = queryDet(q, vs);
      const body = qd ? Cmp('if_commit', [conj([qd.goal, Cmp('\\==', [qd.S, Atom('maybe')])]),
        Cmp('if_commit', [Cmp('==', [qd.S, Atom('yes')]), Cmp('dl_bag_last', [B, list(vs), R]), Cmp('dl_bag_rows', [B, R])]),
        conj([streamed, Cmp('dl_bag_rows', [B, R])])]) : conj([streamed, Cmp('dl_bag_rows', [B, R])]);
      emit(Cmp(':-', [Cmp(q.pred + '__cp', vs.concat([R])), conj([Cmp('dl_query_new', [B]), body])]));
    }

    function queryGoals(q, vs) {
      const rec = ir.get(q.pred + '/' + vs.length); if (!rec || rec.clauses.length !== 1) return null;
      const m = new Map(); const c = P.copy(Cmp(':-', [rec.clauses[0].head, rec.clauses[0].body]), m);
      const h = D(c.a[0]); const ha = h.t === 'c' ? h.a.map(D) : [];
      if (ha.length !== vs.length || ha.some(x => x.t !== 'v') || new Set(ha).size !== ha.length) return null;
      const sub = new Map(ha.map((x, i) => [x, vs[i]]));
      return P.flatConj(P.copy(c.a[1], sub)).map(D);
    }
    function queryS2A(q, vs) {
      const goals = queryGoals(q, vs); if (!goals || goals.length !== 1) return null;
      const g = goals[0]; if (g.t !== 'c' || !user.has(P.key(g)) || !s2aCode.has(P.key(g))) return null;
      if (!vs.every(v => termVars(g).includes(v))) return null;
      return { spec: s2aCode.get(P.key(g)).a[0], args: g.a };
    }
    function queryDet(q, vs) {
      const goals = queryGoals(q, vs);
      if (!goals || !goals.length || !goals.every(g => (user.has(P.key(g)) && detCode.has(P.key(g))) || PURE.has(P.key(g)))) return null;
      const build = (i, Sout) => {
        if (i === goals.length) return Cmp('=', [Sout, Atom('yes')]);
        const g = goals[i];
        if (PURE.has(P.key(g))) return Cmp('if_commit', [g, build(i + 1, Sout), Cmp('=', [Sout, Atom('no')])]);
        const S1 = V('S');
        return conj([Cmp(P.name(g) + '__d', g.a.concat([S1])), Cmp('if_commit', [Cmp('==', [S1, Atom('yes')]), build(i + 1, Sout), Cmp('=', [Sout, S1])])]);
      };
      const S = V('S');
      return { goal: build(0, S), S };
    }

    function hasCut(g) { g = D(g); if (g.t === 'a' && g.n === '!') return true; if (g.t === 'c' && [',', ';', '->', '*->'].includes(g.f)) return g.a.some(hasCut); return false; }
    function kcall(K) { return isTrue(K) ? [] : [Cmp('dl_k', [K])]; }
    function contName(ctx) { return ctx.f + '__c' + (++contN); }

    // the first answer of the conjunction gs followed by K
    function genConj(gs, K, ctx) {
      if (!gs.length) return kcall(K);
      const g = D(gs[0]), rest = gs.slice(1);
      if (isTrue(g)) return genConj(rest, K, ctx);
      if (detGoal(g)) return [g].concat(genConj(rest, K, Object.assign({}, ctx, { outer: ctx.outer.concat(termVars(g)) })));
      // PRUNE pairwise: permutation(L, P), t(P) with t a test over all pairs of positions
      if (rest.length && (isC(g, 'permutation', 2) || (isC(g, P.name(g), 2) && user.has(kk(g)) && P.isPermPred(prog, kk(g)))) && !ctx.noPrune && P.pairwise && prog && isC(rest[0], P.name(rest[0]), 1) && user.has(kk(rest[0])) && D(D(rest[0]).a[0]) === D(g.a[1])) {
        let pw = null; try { pw = P.pairwise(prog, kk(rest[0])); } catch (e) { pw = null; }
        if (pw && pw.vars) return prunePerm(g, rest[0], rest.slice(1), pw, K, ctx);
      }
      if (!rest.length) return genGoal(g, K, ctx);
      // the rest as a continuation term
      const before = new Set(ctx.outer.concat(termVars(g)));
      const rv = termVars(conj(rest));
      const env = rv.filter(v => before.has(v));
      // a rest that can cut: after the cut, a later answer of g must not run it again
      const guarded = !!ctx.cut && rest.some(hasCut);
      if (ctx.cut && !env.includes(ctx.cut)) env.push(ctx.cut);
      const Kr = Cmp(contName(ctx), env.concat([K]));
      const ctx2 = Object.assign({}, ctx, { outer: env.concat(termVars(K)) });
      const rc = genConj(rest, K, ctx2);
      emit(Cmp(':-', [Cmp('dl_k', [Kr]), conj((guarded ? [Cmp('dl_cut_off', [ctx.cut])] : []).concat(rc))]), 'k_cont');
      return genGoal(g, Kr, ctx);
    }

    // the permutation built element by element; a prefix whose new element fails a pair is dropped.  The
    // test is closed under prefixes and select/3 builds permutation/2's lists left to right, so the same
    // permutations pass, in the same order (src/algebra.js).  At run time: an unbound P and a proper L,
    // otherwise the goals as written.
    function prunePerm(g, tg, rest, pw, K, ctx) {
      const L = g.a[0], Pv = g.a[1];
      const Kr = rest.length ? contFor(rest, termVars(Cmp('x', [g, tg])), K, ctx) : K;
      // one pruned generator per test predicate T: T__pwperm(L, Placed, P, K).  The engines that know the
      // source program run it as a native integer loop (detlog_fast.js, cgen.js); this is its definition.
      const T = P.name(tg), nm = T + '__pwperm', pn = T + '__pwpairs', cn = T + '__pwc';
      const general = genConj([g, tg].concat(rest), K, Object.assign({}, ctx, { noPrune: true }));
      const call = [Cmp('if_commit', [conj([Cmp('var', [Pv]), Cmp('is_list', [L])]), Cmp(nm, [L, NIL, Pv, Kr]), conj(general)])];
      if (pwDone.has(T)) return call;
      pwDone.add(T); const pred0 = PRED; PRED = T + '/1';
      const X = V('X'), Xs = V('Xs'), Pre = V('Pre'), Y = V('Y'), Ys = V('Ys'), R = V('R'), K1 = V('K');
      emit(Cmp(':-', [Cmp(nm, [NIL, Var('_'), NIL, K1]), Cmp('dl_k', [K1])]), 'k_prune');
      const K2 = V('K');
      emit(Cmp(':-', [Cmp(nm, [P.cons(X, Xs), Pre, P.cons(Y, Ys), K2]), Cmp('dl_select_k', [P.cons(X, Xs), Y, R, Cmp(cn, [Y, R, Pre, Ys, K2])])]), 'k_prune');
      emit(Cmp(':-', [Cmp('dl_k', [Cmp(cn, [Y, R, Pre, Ys, K2])]), conj([Cmp(pn, [Pre, Y, Int(pw.c0)]), Cmp(nm, [R, P.cons(Y, Pre), Ys, K2])])]), 'k_prune');
      emit(Cmp(pn, [NIL, Var('_'), Var('_')]), 'k_prune');
      const Q = V('Q'), Qs = V('Qs'), Y2 = V('Y'), Dd = V('D'), D1 = V('D');
      const m = new Map([[pw.vars.Q, Q], [pw.vars.Y, Y2], [pw.vars.D, Dd]]);
      const tests = pw.tests.map(t => P.copy(t, m));
      emit(Cmp(':-', [Cmp(pn, [P.cons(Q, Qs), Y2, Dd]), conj(tests.concat([Cmp('is', [D1, Cmp('+', [Dd, Int(1)])]), Cmp(pn, [Qs, Y2, D1])]))]), 'k_prune');
      PRED = pred0;
      return call;
    }

    // the dispatch tests of a predicate's clauses on a bound first argument X, if the clauses are pairwise
    // exclusive there; null otherwise (src/proof.js re-derives the exclusivity)
    function indexTests(cls, X) {
      const tests = [], keys = [];
      for (const c of cls) {
        const h = D(c.head), a = D(h.a[0]);
        if (a.t !== 'v') { keys.push({ pat: a }); tests.push(patTest(a, X)); continue; }
        const g0 = flat(c.body).map(D)[0];
        const iv = g0 && guardInterval(g0, a);
        if (!iv) return null;
        keys.push({ iv }); tests.push(P.copy(g0, new Map([[a, X]])));
      }
      for (let i = 0; i < keys.length; i++) for (let j = i + 1; j < keys.length; j++) if (!P.streamExclusive(keys[i], keys[j])) return null;
      return tests;
    }
    // X has the pattern's principal functor (X is bound here); no binding, no structure built
    function patTest(a, X) {
      return Cmp('dl_has_key', [X, a.t === 'c' ? Cmp(a.f, a.a.map(() => Var('_'))) : a]);
    }

    // findall(T, (between(L, H, I), G1, ..., Gn), Ts) with each Gi a pure builtin or a call of a DET
    // predicate, and T and the Gi using only I, their own variables and ground outer ones: the DET loop
    //   F(I, H, Env.., Ts, S) :- I > H: Ts = []; otherwise the goals' status S1: yes adds T, no skips, maybe
    //   is maybe (and the bag runs instead, from the start)
    // run at the call when L and H are integers and Env is ground.  Each iteration is a fresh activation of
    // F, as each answer of the bag is a fresh copy, so the list is the bag's (k_detloop, src/proof.js).
    function findLoop(T, G, ctx) {
      if (!detCode.size) return null;
      const gs = flat(G).map(D); if (gs.length < 2 || !isC(gs[0], 'between', 3)) return null;
      const I = D(gs[0].a[2]); if (I.t !== 'v' || ctx.outer.includes(I)) return null;
      const body = gs.slice(1);
      if (!body.every(b => PURE.has(kk(b)) || (user.has(kk(b)) && detCode.has(kk(b))))) return null;
      const outerSet = new Set(ctx.outer);
      const used = termVars(Cmp('x', [T, conj(body)]));
      const env = used.filter(v => v !== I && outerSet.has(v));
      if (termVars(Cmp('x', [gs[0].a[0], gs[0].a[1]])).includes(I)) return null;
      const name = ctx.f + '__fl' + (++contN) + '__d';
      const pred0 = PRED; const rule0 = RULE; RULE = 'k_detloop';
      // the clause, over fresh variables
      const m = new Map(); const c = P.copy(Cmp('x', [I, T, conj(body), list(env)]), m);
      const cI = D(c.a[0]), cT = c.a[1], cBody = flat(c.a[2]).map(D), cEnv = listToArray(c.a[3]);
      const H = V('H'), Ts = V('Ts'), Ts1 = V('Ts'), S0 = V('S');
      // each failure point skips the element and each success point adds it, in place (the native tier
      // follows the bindings of one path; a join after the goals would lose them)
      const next = (out) => { const I1 = V('I'); return conj([Cmp('is', [I1, Cmp('+', [cI, Int(1)])]), Cmp(name, [I1, H].concat(cEnv, [out, S0]))]); };
      const skip = () => next(Ts);
      const add = () => Cmp('if_commit', [Cmp('=', [Ts, P.cons(cT, Ts1)]), next(Ts1), Cmp('=', [S0, Atom('no')])]);
      const step = (i) => {
        if (i === cBody.length) return add();
        const b = cBody[i];
        if (PURE.has(kk(b))) return Cmp('if_commit', [b, step(i + 1), skip()]);
        const S2 = V('S');
        return conj([Cmp(P.name(b) + '__d', b.a.concat([S2])), Cmp('if_commit', [Cmp('=', [S2, Atom('yes')]), step(i + 1),
          Cmp('if_commit', [Cmp('=', [S2, Atom('no')]), skip(), Cmp('=', [S0, S2])])])]);
      };
      emit(Cmp(':-', [Cmp(name, [cI, H].concat(cEnv, [Ts, S0])),
        Cmp('if_commit', [Cmp('>', [cI, H]), Cmp('if_commit', [Cmp('=', [Ts, NIL]), Cmp('=', [S0, Atom('yes')]), Cmp('=', [S0, Atom('no')])]), step(0)])]));
      RULE = rule0; PRED = pred0;
      const Lo = gs[0].a[0], Hi = gs[0].a[1], R = V('Ts'), S = V('S');
      const cond = [Cmp('integer', [Lo]), Cmp('integer', [Hi])].concat(env.length ? [Cmp('ground', [list(env)])] : [],
        [Cmp(name, [Lo, Hi].concat(env, [R, S])), Cmp('==', [S, Atom('yes')])]);
      return { cond, Ts: R };
    }

    // the continuation for rest, after the goals whose variables are bound
    function contFor(rest, bound, K, ctx) {
      const before = new Set(ctx.outer.concat(bound));
      const env = termVars(conj(rest)).filter(v => before.has(v));
      const guarded = !!ctx.cut && rest.some(hasCut);
      if (ctx.cut && !env.includes(ctx.cut)) env.push(ctx.cut);
      const Kr = Cmp(contName(ctx), env.concat([K]));
      const rc = genConj(rest, K, Object.assign({}, ctx, { outer: env.concat(termVars(K)) }));
      emit(Cmp(':-', [Cmp('dl_k', [Kr]), conj((guarded ? [Cmp('dl_cut_off', [ctx.cut])] : []).concat(rc))]), 'k_cont');
      return Kr;
    }

    function detGoal(g) {
      const k = kk(g);
      if (user.has(k)) return false;
      if ([',/2', ';/2', '->/2', '*->/2', '\\+/1', 'findall/3', 'findall/4', 'aggregate_all/3', '!/0', 'once/1', 'ignore/1', 'forall/2', 'call/1', 'not/1'].includes(k)) return false;
      const bk = P.biKind ? P.biKind(k, g) : null;
      return bk === 'det' || bk === 'effect' || bk === 'dbeffect' || k === 'fail/0' || k === 'false/0';
    }

    // one goal followed by K
    function genGoal(g, K, ctx) {
      g = D(g); const k = kk(g);
      switch (k) {
        case 'true/0': return kcall(K);
        case 'fail/0': case 'false/0': return [P.FAIL];
        case ',/2': return genConj(flat(g), K, ctx);
        case '!/0': if (!ctx.cut) throw new Error(ctx.f + ': cut outside a clause'); return [Cmp('dl_cut_set', [ctx.cut])].concat(kcall(K));
        case '->/2': return [Cmp('if_commit', [conj(genConj(flat(g.a[0]), TRUE, ctx)), conj(genConj(flat(g.a[1]), K, ctx)), P.FAIL])];
        case ';/2': {
          const l = D(g.a[0]);
          if (isC(l, '->', 2)) return [Cmp('if_commit', [conj(genConj(flat(l.a[0]), TRUE, ctx)), conj(genConj(flat(l.a[1]), K, ctx)), conj(genConj(flat(g.a[1]), K, ctx))])];
          const alts = []; (function fl(x) { x = D(x); if (isC(x, ';', 2) && !isC(x.a[0], '->', 2)) { alts.push(x.a[0]); fl(x.a[1]); } else alts.push(x); })(g);
          let ch = conj(genGoal(alts[alts.length - 1], K, ctx));
          for (let j = alts.length - 2; j >= 0; j--) ch = Cmp('if_commit', [conj(genGoal(alts[j], K, ctx)), TRUE, ctx.cut ? conj([Cmp('dl_cut_off', [ctx.cut]), ch]) : ch]);
          return [ch];
        }
        case '\\+/1': case 'not/1': return [Cmp('if_commit', [conj(genConj(flat(g.a[0]), TRUE, ctx)), P.FAIL, TRUE])].concat(kcall(K));
        case 'once/1': return genConj(flat(g.a[0]), TRUE, ctx).concat(kcall(K));
        case 'ignore/1': return [Cmp('if_commit', [conj(genConj(flat(g.a[0]), TRUE, ctx)), TRUE, TRUE])].concat(kcall(K));
        case 'forall/2': return genGoal(Cmp('\\+', [Cmp(',', [g.a[0], Cmp('\\+', [g.a[1]])])]), K, ctx);
        case 'call/1': return genGoal(g.a[0], K, ctx);
        case 'findall/3': case 'findall/4': {
          // MNN: findall/3 over between/3 and DET calls is a deterministic loop (the native tier's integer loop)
          const fl = k === 'findall/3' ? findLoop(g.a[0], g.a[1], ctx) : null;
          const B = V('B');
          const coll = [Cmp('dl_bag_new', [B]), Cmp('if_commit', [conj(genConj(flat(g.a[1]), Cmp('dl_collect', [B, g.a[0]]), ctx)), TRUE, TRUE])];
          const res = k === 'findall/3' ? Cmp('dl_bag_list', [B, g.a[2]]) : Cmp('dl_bag_list', [B, g.a[2], g.a[3]]);
          if (fl) return [Cmp('if_commit', [conj(fl.cond), conj([Cmp('=', [fl.Ts, g.a[2]])].concat(kcall(K))), conj(coll.concat([res], kcall(K)))])];
          return coll.concat([res], kcall(K));
        }
        case 'aggregate_all/3': {
          const spec = D(g.a[0]);
          const name = spec.t === 'a' ? spec.n : spec.f;
          const tmpl = spec.t === 'c' && spec.a.length === 1 ? spec.a[0] : TRUE;
          const B = V('B'), Ts = V('Ts');
          return [Cmp('dl_bag_new', [B]), Cmp('if_commit', [conj(genConj(flat(g.a[1]), Cmp('dl_collect', [B, tmpl]), ctx)), TRUE, TRUE]),
            Cmp('dl_bag_list', [B, Ts]), Cmp('aggregate_list', [Atom(name), Ts, g.a[2]])].concat(kcall(K));
        }
      }
      if (user.has(k)) {
        const as = g.t === 'c' ? g.a : [];
        return [Cmp(kname(P.name(g)), as.concat([K]))];
      }
      if (LIB_GEN[k] && g.t === 'c') return [Cmp(P.name(LIB_GEN[k](g)), LIB_GEN[k](g).a.concat([K]))];
      const bk = P.biKind ? P.biKind(k, g) : null;
      if (bk === 'nondet') { const Rs = V('Rs'); return [Cmp('builtin_rows', [g, Rs]), Cmp('dl_rows_k', [Rs, list([g]), K])]; }
      return [g].concat(kcall(K));
    }

    const res = { clauses, tags };
    res.text = printStreams(res);
    return res;
  }

  // ---- runtime builtins shared by every engine (reference, closure, JIT) ----
  const B = P.builtins;
  // a bag and a cut cell are terms '$bag'(N) / '$cut'(N) carrying a JavaScript slot that the builtins
  // mutate: nothing outlives the terms (no global table), and a cell is not undone on backtracking
  const det = (k, fn) => { B[k] = { fn }; };
  const outOf = e => (typeof e.out === 'string' ? e.out : '');
  let cellN = 0;
  const cell = (f, slot) => { const t = Cmp(f, [Int(++cellN)]); t.slot = slot; return t; };
  const slotOf = (t, f) => { t = D(t); if (t.t !== 'c' || t.f !== f || !t.slot) throw new Error(f + ': not a cell'); return t.slot; };
  det('dl_bag_new/1', (a, e) => e.unify(a[0], cell('$bag', { items: [], mark: outOf(e).length })));
  // the query boundary's bag: the same here (the SWI-Prolog runtime also captures the output there)
  det('dl_query_new/1', (a, e) => e.unify(a[0], cell('$bag', { items: [], mark: outOf(e).length })));
  det('dl_bag_add/2', (a) => { slotOf(a[0], '$bag').items.push(P.copy(a[1])); return true; });
  det('dl_bag_list/2', (a, e) => { const b = slotOf(a[0], '$bag'); const it = b.items; b.items = []; return e.unify(a[1], list(it)); });
  det('dl_bag_list/3', (a, e) => { const b = slotOf(a[0], '$bag'); const it = b.items; b.items = []; let r = a[2]; for (let i = it.length - 1; i >= 0; i--) r = P.cons(it[i], r); return e.unify(a[1], r); });
  // query rows: the text written since the previous row becomes an out(Text) item before it
  const takeText = (b, e) => { const o = outOf(e); if (o.length > b.mark) { b.items.push(Cmp('out', [Str(o.slice(b.mark))])); e.out = o.slice(0, b.mark); } };
  det('dl_bag_row/2', (a, e) => { const b = slotOf(a[0], '$bag'); takeText(b, e); b.items.push(Cmp('e', [P.copy(a[1])])); return true; });
  det('dl_bag_rows/2', (a, e) => { const b = slotOf(a[0], '$bag'); takeText(b, e); const it = b.items; b.items = []; return e.unify(a[1], list(it)); });
  det('dl_cut_new/1', (a, e) => e.unify(a[0], cell('$cut', { cut: false })));
  det('dl_cut_set/1', (a) => { slotOf(a[0], '$cut').cut = true; return true; });
  det('dl_cut_off/1', (a) => !slotOf(a[0], '$cut').cut);

  // X bound, with the principal functor of P (name and arity; an atomic P: X is that constant)
  const sameKey = (x, p) => { x = D(x); p = D(p); if (x.t === 'v') return false; if (p.t === 'c') return x.t === 'c' && x.f === p.f && x.a.length === p.a.length;
    if (x.t !== p.t) return false; return p.t === 'a' ? x.n === p.n : p.t === 'n' ? x.v === p.v && !!x.f === !!p.f : p.t === 's' ? x.v === p.v : false; };
  det('dl_has_key/2', (a) => sameKey(a[0], a[1]));
  det('dl_bag_count/2', (a, e) => { const b = slotOf(a[0], '$bag'); let n = 0; for (const x of b.items) if (x.f === 'e') n++; return e.unify(a[1], Int(n)); });
  // for the interpreter's per-call route (src/interp.js): a bag made from JavaScript, and its items with the
  // text written after the last answer
  P.streamBag = () => cell('$bag', { items: [], mark: 0 });
  P.streamBagItems = (b, out) => { const sl = slotOf(b, '$bag'); const it = sl.items.slice(); if (out && out.length > sl.mark) it.push(Cmp('out', [Str(out.slice(sl.mark))])); return it; };
  det('dl_bag_last/3', (a, e) => { const b = slotOf(a[0], '$bag'); takeText(b, e); b.items.push(Cmp('e', [a[1]])); const it = b.items; b.items = []; return e.unify(a[2], list(it)); });

  // the text of stream code, without the clauses of the predicates in drop (keys p/n)
  function printStreams(st, drop) {
    const keep = st.clauses.filter((c, i) => !(drop && drop.has(st.tags[i].pred)));
    return '% Detlog stream code: no answer packets (src/stream.js)\n' + LIB + '\n' + keep.map(c => P.showClause(c, { varName: v => v.name })).join('\n') + '\n';
  }

  // an arithmetic guard on V against an integer: the interval of V it admits, {lo, hi, loOpen, hiOpen}
  function guardInterval(g, v) {
    g = D(g); if (g.t !== 'c' || g.a.length !== 2) return null;
    const ops = { '>': 1, '>=': 1, '<': 1, '=<': 1, '=:=': 1 };
    if (!ops[g.f]) return null;
    let [l, r] = g.a.map(D), op = g.f;
    const flip = { '>': '<', '<': '>', '>=': '=<', '=<': '>=', '=:=': '=:=' };
    if (r === v && l.t === 'n') { [l, r] = [r, l]; op = flip[op]; }
    if (l !== v || r.t !== 'n' || r.f || !Number.isSafeInteger(r.v)) return null;
    const c = r.v;
    if (op === '>') return { lo: c, loOpen: true, hi: Infinity, hiOpen: true };
    if (op === '>=') return { lo: c, loOpen: false, hi: Infinity, hiOpen: true };
    if (op === '<') return { lo: -Infinity, loOpen: true, hi: c, hiOpen: true };
    if (op === '=<') return { lo: -Infinity, loOpen: true, hi: c, hiOpen: false };
    return { lo: c, loOpen: false, hi: c, hiOpen: false };
  }
  const inIv = (iv, x) => (iv.loOpen ? x > iv.lo : x >= iv.lo) && (iv.hiOpen ? x < iv.hi : x <= iv.hi);
  // two clause keys ({pat} a first-argument pattern, {iv} a guard interval) that no bound argument satisfies
  // both of: different principal functors; an integer pattern outside the interval; disjoint intervals
  P.streamExclusive = (a, b) => {
    if (a.pat && b.pat) {
      const x = D(a.pat), y = D(b.pat);
      if (x.t === 'c' && y.t === 'c') return x.f !== y.f || x.a.length !== y.a.length;
      if (x.t === 'c' || y.t === 'c') return true;
      if (x.t !== y.t) return x.t === 'n' && y.t === 'n' ? false : true;
      return x.t === 'a' ? x.n !== y.n : x.t === 'n' ? (x.v !== y.v || !!x.f !== !!y.f) : x.t === 's' ? x.v !== y.v : false;
    }
    if (a.iv && b.iv) { const lo = a.iv.lo > b.iv.lo ? a.iv : b.iv, hi = a.iv.hi < b.iv.hi ? a.iv : b.iv;
      return lo.lo > hi.hi || (lo.lo === hi.hi && (lo.loOpen || hi.hiOpen)); }
    const p = D((a.pat || b.pat)), iv = a.iv || b.iv;
    return p.t === 'n' && !p.f && Number.isSafeInteger(p.v) && !inIv(iv, p.v);
  };

  // a user predicate that is permutation/2, in permutation/2's order: perm([], []).  perm(L, [H|T]) :-
  // S(H, L, R), perm(R, T).  with S select/3 or a user predicate that is select/3:
  // s(X, [X|T], T).  s(X, [H|T], [H|R]) :- s(X, T, R).  (Variables as shown; any names.)
  const vv = x => D(x).t === 'v';
  const isA = (t, n) => { t = D(t); return t.t === 'a' && t.n === n; };
  function isSelectPred(prog, k) {
    const cls = prog.preds.get(k); if (!cls || cls.length !== 2) return false;
    const [a, b] = cls.map(c => ({ h: D(c.head), b: D(c.body) }));
    if (!isTrue(a.b) || a.h.t !== 'c' || a.h.a.length !== 3) return false;
    const [X, L1, T1] = a.h.a.map(D);
    if (!vv(X) || !vv(T1) || !(L1.t === 'c' && L1.f === '.' && D(L1.a[0]) === X && D(L1.a[1]) === T1)) return false;
    const [X2, L2, L3] = b.h.a.map(D);
    if (!vv(X2) || L2.t !== 'c' || L2.f !== '.' || L3.t !== 'c' || L3.f !== '.') return false;
    const H = D(L2.a[0]), T = D(L2.a[1]), R = D(L3.a[1]);
    if (!vv(H) || !vv(T) || !vv(R) || D(L3.a[0]) !== H || new Set([X2, H, T, R]).size !== 4) return false;
    return isC(b.b, b.h.f, 3) && D(b.b.a[0]) === X2 && D(b.b.a[1]) === T && D(b.b.a[2]) === R;
  }
  P.isPermPred = (prog, k) => {
    const cls = prog && prog.preds.get(k); if (!cls || cls.length !== 2) return false;
    const [a, b] = cls.map(c => ({ h: D(c.head), b: D(c.body) }));
    if (!isTrue(a.b) || !a.h.a.every(x => isA(x, '[]'))) return false;
    const [L, PT] = b.h.a.map(D); if (!vv(L) || PT.t !== 'c' || PT.f !== '.') return false;
    const H = D(PT.a[0]), T = D(PT.a[1]); if (!vv(H) || !vv(T)) return false;
    const gs = P.flatConj(b.b).map(D); if (gs.length !== 2) return false;
    const [s1, s2] = gs; if (!isC(s1, P.name(s1), 3) || !isC(s2, b.h.f, 2)) return false;
    const R = D(s1.a[2]);
    if (D(s1.a[0]) !== H || D(s1.a[1]) !== L || !vv(R) || D(s2.a[0]) !== R || D(s2.a[1]) !== T || new Set([L, H, T, R]).size !== 4) return false;
    return s1.f === 'select' || isSelectPred(prog, P.key(s1));
  };

  P.toStreams = toStreams; P.printStreams = printStreams;
  P.STREAM_LIB = LIB;
})(typeof globalThis !== 'undefined' ? (globalThis.PL2D = globalThis.PL2D || {}) : this);
