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
   and the text written before each one (dl_bag_row/2), so every consumer of query packets is unchanged.
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

  function toStreams(conv, opts) {
    opts = opts || {};
    const ir = conv.ir;
    const clauses = []; // [term]
    const user = new Set(ir.keys());
    const emit = t => clauses.push(t);
    const kname = f => f + '__k';
    let contN = 0, varN = 0;
    const V = p => Var(p + '__' + (++varN));

    for (const [k, rec] of ir) {
      const i = k.lastIndexOf('/'); const f = k.slice(0, i), n = +k.slice(i + 1);
      const A = []; for (let j = 0; j < n; j++) A.push(Var('A__' + (j + 1)));
      const KV = Var('K__0');
      const head = Cmp(kname(f), A.concat([KV]));
      if (rec.error) { emit(Cmp(':-', [head, Cmp('detlog_unsupported', [Cmp('/', [Atom(f), Int(n)]), Str(rec.error)])])); continue; }
      const cls = rec.clauses;
      if (!cls.length) { emit(Cmp(':-', [head, P.FAIL])); continue; }
      // facts: a table walked by the stream library
      if (cls.length > 1 && cls.every(c => isTrue(c.body))) {
        const rows = cls.map(c => list(D(c.head).t === 'c' ? D(c.head).a : []));
        emit(Cmp(':-', [head, Cmp('dl_facts_k', [list(rows), list(A), KV])]));
        continue;
      }
      const cut = cls.some(c => hasCut(c.body));
      const C = Var('C__0');
      const clauseGoal = (c, j) => {
        const m = new Map(); const t = P.copy(Cmp(':-', [c.head, c.body]), m);
        const h = D(t.a[0]); const hargs = h.t === 'c' ? h.a : [];
        const K1 = V('K'), C1 = cut ? V('C') : null;
        const ctx = { f, cut: C1, outer: termVars(Cmp('h', hargs.concat([K1]))) };
        const body = genConj(flat(t.a[1]), K1, ctx);
        const cname = cls.length === 1 ? kname(f) : kname(f) + (j + 1);
        emit(Cmp(':-', [Cmp(cname, hargs.concat(C1 ? [C1, K1] : [K1])), conj(body)]));
        return Cmp(cname, A.concat(cut ? [C, KV] : [KV]));
      };
      if (cls.length === 1 && !cut) { clauseGoal(cls[0], 0); continue; }
      const calls = cls.map(clauseGoal);
      let chain = calls[calls.length - 1];
      for (let j = calls.length - 2; j >= 0; j--) chain = Cmp('if_commit', [calls[j], TRUE, cut ? conj([Cmp('dl_cut_off', [C]), chain]) : chain]);
      emit(Cmp(':-', [head, cut ? conj([Cmp('dl_cut_new', [C]), chain]) : chain]));
    }

    // queries: the packet entry, collecting answers and the text written before each
    for (const q of conv.queries || []) {
      const vs = q.vars.map(v => Var(v));
      const B = V('B'), R = V('R');
      emit(Cmp(':-', [Cmp(q.pred + '__cp', vs.concat([R])), conj([Cmp('dl_bag_new', [B]),
        Cmp('if_commit', [Cmp(kname(q.pred), vs.concat([Cmp('dl_row', [B, list(vs)])])), TRUE, TRUE]), Cmp('dl_bag_rows', [B, R])])]));
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
      emit(Cmp(':-', [Cmp('dl_k', [Kr]), conj((guarded ? [Cmp('dl_cut_off', [ctx.cut])] : []).concat(rc))]));
      return genGoal(g, Kr, ctx);
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
          const B = V('B');
          const coll = [Cmp('dl_bag_new', [B]), Cmp('if_commit', [conj(genConj(flat(g.a[1]), Cmp('dl_collect', [B, g.a[0]]), ctx)), TRUE, TRUE])];
          const res = k === 'findall/3' ? Cmp('dl_bag_list', [B, g.a[2]]) : Cmp('dl_bag_list', [B, g.a[2], g.a[3]]);
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

    const text = '% Detlog stream code: no answer packets (src/stream.js)\n' + LIB + '\n' +
      clauses.map(c => P.showClause(c, { varName: v => v.name })).join('\n') + '\n';
    return { text, clauses };
  }

  // ---- runtime builtins shared by every engine (reference, closure, JIT) ----
  const B = P.builtins;
  const bags = new Map(); let bagN = 0;
  const cuts = new Map(); let cutN = 0;
  const det = (k, fn) => { B[k] = { fn }; };
  const outOf = e => (typeof e.out === 'string' ? e.out : '');
  det('dl_bag_new/1', (a, e) => { const id = ++bagN; bags.set(id, { items: [], mark: outOf(e).length }); return e.unify(a[0], Int(id)); });
  det('dl_bag_add/2', (a) => { const b = bags.get(D(a[0]).v); b.items.push(P.copy(a[1])); return true; });
  det('dl_bag_list/2', (a, e) => { const b = bags.get(D(a[0]).v); bags.delete(D(a[0]).v); return e.unify(a[1], list(b.items)); });
  det('dl_bag_list/3', (a, e) => { const b = bags.get(D(a[0]).v); bags.delete(D(a[0]).v); let r = a[2]; for (let i = b.items.length - 1; i >= 0; i--) r = P.cons(b.items[i], r); return e.unify(a[1], r); });
  // query rows: the text written since the previous row becomes an out(Text) item before it
  const takeText = (b, e) => { const o = outOf(e); if (o.length > b.mark) { b.items.push(Cmp('out', [Str(o.slice(b.mark))])); e.out = o.slice(0, b.mark); } };
  det('dl_bag_row/2', (a, e) => { const b = bags.get(D(a[0]).v); takeText(b, e); b.items.push(Cmp('e', [P.copy(a[1])])); return true; });
  det('dl_bag_rows/2', (a, e) => { const b = bags.get(D(a[0]).v); takeText(b, e); bags.delete(D(a[0]).v); return e.unify(a[1], list(b.items)); });
  det('dl_cut_new/1', (a, e) => { const id = ++cutN; cuts.set(id, false); return e.unify(a[0], Int(id)); });
  det('dl_cut_set/1', (a) => { cuts.set(D(a[0]).v, true); return true; });
  det('dl_cut_off/1', (a) => !cuts.get(D(a[0]).v));

  P.toStreams = toStreams;
  P.STREAM_LIB = LIB;
})(typeof globalThis !== 'undefined' ? (globalThis.PL2D = globalThis.PL2D || {}) : this);
