/* pl2detlog back-converter: Detlog -> Prolog.
   Works from the Detlog text alone (so edited Detlog can be back-converted): each generated template is
   recognised and turned back into the Prolog goal it computes.  Cuts are restored from the if_commit chains
   of rule CUT, specialised maplist/foldl closures are folded back, S2A loops become formulas or facts and
   memo wrappers are dropped.  Every change from the original source is reported as a warning. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, listToArray, copy, termVars, show } = P;
  const D = deref;
  const conj = P.conjT;
  const isA = (t, n) => { t = D(t); return t.t === 'a' && t.n === n; };
  const isC = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && (n === undefined || t.a.length === n); };
  const flat = g => P.flatConj(g);

  function BackError(msg) { const e = new Error(msg); e.back = true; return e; }

  function backConvert(detlogText, opts) {
    opts = opts || {};
    const prog = P.loadProgram(detlogText);
    const res = { clauses: [], warnings: [], notes: [], preds: [], queries: [], text: '' };
    const cpPreds = prog.order.filter(k => /__cp\/\d+$/.test(k));
    const specInfo = new Map(); // spec pred key -> {kind, closureClause}
    const predClauses = new Map(); // p/n -> [clause terms]
    const predNotes = new Map();
    const note = (k, m) => { if (!predNotes.has(k)) predNotes.set(k, []); if (!predNotes.get(k).includes(m)) predNotes.get(k).push(m); };
    const getCls = k => { const c = prog.preds.get(k); if (!c) throw BackError('missing Detlog predicate ' + k); return c; };

    // stream code (src/stream.js): every predicate p/n is p__k/n+1
    const streams = (prog.preds.get('dl_k/1') || []).some(c => isC(D(c.head).a[0], 'dl_row', 2));
    const topKeys = streams ? prog.order.filter(k => /__k\/\d+$/.test(k) && !/^dl_/.test(k)) : cpPreds;
    for (const k of topKeys) {
      const [f, nS] = splitKey(k); const n = +nS - 1; const pname = f.replace(streams ? /__k$/ : /__cp$/, ''); const pk = pname + '/' + n;
      try {
        const clauses = streams ? decompStreamPred(k, pk, pname) : decompPacketPred(k, pk);
        predClauses.set(pk, clauses);
      } catch (e) {
        if (!e.back) throw e;
        res.warnings.push({ pred: pk, kind: 'error', msg: 'not back-convertible: ' + e.message });
        predClauses.set(pk, null);
      }
    }

    // ---- stream code back to Prolog ----
    // p__k(A.., K): an S2A table, a facts table, a DET or MEMO wrapper (dropped), or the clause chain
    //   [dl_cut_new(C),] if_commit(p__k1(A.., [C,] K), true, [dl_cut_off(C),] ...)
    // whose clauses are walked goal by goal, following each continuation term into its dl_k/1 clause.
    var kcMap = null; // continuation functor -> its dl_k/1 clause
    function kconts() { if (!kcMap) { kcMap = new Map(); for (const c of prog.preds.get('dl_k/1') || []) { const a = D(D(c.head).a[0]); if (a.t === 'c') kcMap.set(a.f + '/' + a.a.length, c); } } return kcMap; }
    function lastArg(t) { t = D(t); return t.a[t.a.length - 1]; }
    function decompStreamPred(k, pk, pname) {
      const cls = getCls(k);
      if (cls.length === 1) {
        const h = D(cls[0].head), gs = flat(cls[0].body).map(D), A = h.a.slice(0, -1);
        if (gs.length === 2 && isC(gs[0], 's2a_rows', 3) && isC(gs[1], 'dl_rows_k', 3)) { note(pk, 'S2A loop back-converted'); return s2aClauses(gs[0].a[0], pname, A.length, pk); }
        if (gs.length === 1 && isC(gs[0], 'dl_facts_k', 3)) return listToArray(gs[0].a[0]).map(r => ({ head: Cmp(pname, listToArray(r).map(x => copy(x))), body: P.TRUE }));
        // DET wrapper: if_commit((p__d(A.., S), S \== maybe), (S == yes, dl_k(K)), Stream)
        if (gs.length === 1 && isC(gs[0], 'if_commit', 3)) {
          const c0 = flat(gs[0].a[0]).map(D);
          if (c0.length === 2 && c0[0].t === 'c' && /__d$/.test(c0[0].f) && isC(c0[1], '\\==', 2)) {
            note(pk, 'deterministic mode dropped (DET is an optimisation only)');
            return decompStreamPred(P.key(gs[0].a[2]), pk, pname);
          }
        }
        // MEMO wrapper: memo_lookup(p/n, A, F), p__kmemo(F, A.., K); its none clause runs the stream into a bag
        if (gs.length === 2 && isC(gs[0], 'memo_lookup', 3)) {
          note(pk, 'memo table dropped (memoisation is an optimisation only)');
          const none = getCls(P.key(gs[1])).find(c => isA(D(c.head).a[0], 'none'));
          if (!none) throw BackError('memo wrapper without a none clause');
          const ic = flat(none.body).map(D).find(g => isC(g, 'if_commit', 3));
          return decompStreamPred(P.key(ic.a[0]), pk, pname);
        }
      }
      // the clause chain, or the predicate's only clause
      const chainOf = (g, out) => { g = D(g);
        // first-argument dispatch (k_index): its else branch is the chain of all the clauses
        if (isC(g, 'if_commit', 3) && isC(g.a[0], 'nonvar', 1) && !out.length) return chainOf(g.a[2], out);
        if (isC(g, ',', 2) && isC(D(g.a[0]), 'dl_cut_off', 1)) return chainOf(g.a[1], out);
        if (isC(g, 'if_commit', 3) && isA(g.a[1], 'true') && D(g.a[0]).t === 'c' && prog.preds.has(P.key(g.a[0])) && /__k\w*\d+$/.test(D(g.a[0]).f)) { out.push(P.key(g.a[0])); return chainOf(g.a[2], out); }
        if (g.t === 'c' && prog.preds.has(P.key(g)) && /__k\w*\d+$/.test(g.f)) { out.push(P.key(g)); return out; }
        return null; };
      if (cls.length === 1) {
        const gs = flat(cls[0].body).map(D);
        const cut = gs.length === 2 && isC(gs[0], 'dl_cut_new', 1);
        const ch = gs.length === 1 || cut ? chainOf(gs[gs.length - 1], []) : null;
        if (ch) { const out = []; for (const ck of ch) for (const c of getCls(ck)) out.push(...streamClause(c, pname, pk, cut)); return out; }
      }
      const out = []; for (const c of cls) out.push(...streamClause(c, pname, pk, false)); return out;
    }
    function streamClause(cl, pname, pk, cut) {
      const m = new Map(); const t = copy(Cmp(':-', [cl.head, cl.body]), m);
      const h = D(t.a[0]); const K = h.a[h.a.length - 1], C = cut ? h.a[h.a.length - 2] : null;
      const args = h.a.slice(0, cut ? -2 : -1);
      const body = walkK(flat(t.a[1]), K, C);
      const names = new Map();
      const clause = { head: Cmp(pname, args.map(x => ren(x, names))), body: ren(body, names) };
      return restoreCuts(clause, pname, pk).map(c => cleanup(c, pk));
    }
    // the Prolog goal of a stream goal sequence ending in the terminal continuation T
    function walkK(gs, T, C) {
      gs = gs.map(D); const out = [];
      const isT = x => sameT(x, T);
      for (let i = 0; i < gs.length; i++) {
        const g = gs[i], last = i === gs.length - 1;
        if (isC(g, 'dl_k', 1)) { if (isT(g.a[0])) continue; out.push(cont(g.a[0], T, C)); continue; }
        if (isC(g, 'dl_cut_off', 1)) continue;
        if (isC(g, 'dl_cut_set', 1)) { out.push(Atom('!')); continue; }
        // findall/3, findall/4, aggregate_all/3 through a bag
        if (isC(g, 'dl_bag_new', 1) && isC(gs[i + 1], 'if_commit', 3) && (isC(gs[i + 2], 'dl_bag_list', 2) || isC(gs[i + 2], 'dl_bag_list', 3))) {
          const ic = D(gs[i + 1]), bl = D(gs[i + 2]);
          const term = (function find(x) { x = D(x); if (isC(x, 'dl_collect', 2)) return x; if (x.t === 'c') for (const y of x.a) { const r = find(y); if (r) return r; } return null; })(ic.a[0]);
          const inner = walkK(flat(ic.a[0]), term, C);
          if (isC(gs[i + 3], 'aggregate_list', 3) && D(gs[i + 3].a[1]) === D(bl.a[1])) {
            const ag = D(gs[i + 3]), nm = D(ag.a[0]).n, tm = term.a[1];
            out.push(Cmp('aggregate_all', [isA(tm, 'true') && nm === 'count' ? Atom('count') : Cmp(nm, [tm]), inner, ag.a[2]])); i += 3; continue;
          }
          out.push(bl.a.length === 2 ? Cmp('findall', [term.a[1], inner, bl.a[1]]) : Cmp('findall', [term.a[1], inner, bl.a[1], bl.a[2]])); i += 2; continue;
        }
        if (isC(g, 'builtin_rows', 2) && isC(gs[i + 1], 'dl_rows_k', 3)) { out.push(g.a[0]); const k2 = gs[i + 1].a[2]; i++; if (!isT(k2)) out.push(cont(k2, T, C)); continue; }
        if (isC(g, 'if_commit', 3)) {
          const c0 = flat(g.a[0]).map(D);
          // the pruned permutation: the goals as written are its else branch
          if (c0.length === 2 && isC(c0[0], 'var', 1) && isC(c0[1], 'is_list', 1) && D(g.a[1]).t === 'c' && /__pwperm$/.test(D(g.a[1]).f)) { out.push(walkK(flat(g.a[2]), T, C)); continue; }
          // the DET loop for findall/3 over between/3: the goals as written are its else branch
          if (c0.some(x => x.t === 'c' && /__fl\d+__d$/.test(x.f))) { out.push(walkK(flat(g.a[2]), T, C)); continue; }
          const reaches = x => { let r = false; (function w(y) { y = D(y); if (sameT(y, T) && !isA(y, 'true')) r = true; else if (y.t === 'c') y.a.forEach(w); })(x); return r; };
          if (isA(g.a[1], 'true') && reaches(g.a[0])) { out.push(Cmp(';', [walkK(flat(g.a[0]), T, C), walkK(flat(g.a[2]), T, C)])); continue; }
          const cond = walkK(flat(g.a[0]), Atom('true'), C);
          out.push(mkIte(cond, walkK(flat(g.a[1]), T, C), walkK(flat(g.a[2]), T, C))); continue;
        }
        // a stream call: its goal, then its continuation (to T), or once/1 when goals follow it
        const sc = streamCall(g);
        if (sc) {
          const kt = lastArg(g);
          if (last) { out.push(sc); if (!isT(kt)) out.push(cont(kt, T, C)); }
          else { const inner = isA(kt, 'true') ? sc : conj([sc, cont(kt, Atom('true'), C)]); out.push(Cmp('once', [inner])); }
          continue;
        }
        out.push(g);
      }
      return conj(out);
    }
    function streamCall(g) {
      g = D(g); if (g.t !== 'c') return null; const a = g.a;
      if (g.f === 'dl_member_k' && a.length === 3) return Cmp('member', [a[1], a[0]]);
      if (g.f === 'dl_between_k' && a.length === 4) return Cmp('between', [a[0], a[1], a[2]]);
      if (g.f === 'dl_select_k' && a.length === 4) return Cmp('select', [a[1], a[0], a[2]]);
      if (g.f === 'dl_nth_k' && a.length === 5) return Cmp(D(a[1]).v === 0 ? 'nth0' : 'nth1', [a[2], a[0], a[3]]);
      if (/__k$/.test(g.f) && prog.preds.has(P.key(g))) { const f = g.f.slice(0, -3); return a.length === 1 ? Atom(f) : Cmp(f, a.slice(0, -1)); }
      return null;
    }
    function sameT(a, b) {
      a = D(a); b = D(b); if (a === b) return true; if (a.t !== b.t) return false;
      if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => sameT(x, b.a[i]));
      return a.t === 'a' ? a.n === b.n : a.t === 'n' ? a.v === b.v : a.t === 's' ? a.v === b.v : false;
    }
    // unify a fresh clause head with a term (the head's variables are fresh: no undo is needed)
    function bindTo(a, b) {
      a = D(a); b = D(b); if (a === b) return true;
      if (a.t === 'v') { a.ref = b; return true; } if (b.t === 'v') { b.ref = a; return true; }
      if (a.t !== b.t) return false;
      if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => bindTo(x, b.a[i]));
      return a.t === 'a' ? a.n === b.n : a.t === 'n' ? a.v === b.v && !!a.f === !!b.f : a.t === 's' ? a.v === b.v : false;
    }
    // the rest a continuation term stands for
    function cont(kt, T, C) {
      kt = D(kt); if (sameT(kt, T)) return P.TRUE;
      const kc = kt.t === 'c' ? kconts().get(kt.f + '/' + kt.a.length) : null;
      if (!kc) throw BackError('unknown continuation ' + show(kt));
      const c = copy(Cmp(':-', [kc.head, kc.body]));
      if (!bindTo(D(D(c.a[0]).a[0]), kt)) throw BackError('continuation ' + show(kt) + ' does not match its clause');
      return walkK(flat(c.a[1]), T, C);
    }

    // decompile the packet predicate k (p__cp/n+1) into Prolog clauses of p/n
    function decompPacketPred(k, pk) {
      const cls = getCls(k);
      if (cls.length !== 1) throw BackError(k + ' has ' + cls.length + ' clauses (expected one)');
      return decompPacketClause(cls[0], pk, P.name(cls[0].head).replace(/__cp$/, ''));
    }
    function decompPacketClause(cl, pk, pname) {
      const head = D(cl.head); const A = head.a.slice(0, -1); const Rows = head.a[head.a.length - 1];
      const gs = flat(cl.body);
      const b0 = D(gs[0]);
      // empty / dynamic
      if (gs.length === 1 && isC(b0, '=', 2) && D(b0.a[0]) === D(Rows) && isA(b0.a[1], '[]')) { note(pk, 'no clauses'); return []; }
      // unsupported
      if (isC(b0, 'detlog_unsupported', 2)) throw BackError('the predicate was not converted (' + P.textOf(b0.a[1]) + ')');
      // FACTS
      if (gs.length === 1 && isC(b0, 'cp_filter', 3)) {
        return listToArray(b0.a[0]).map(r => { const args = listToArray(D(r).a[0]); return { head: Cmp(pname, args.map(x => copy(x))), body: P.TRUE }; });
      }
      // S2A
      if (gs.length === 1 && isC(b0, 's2a_rows', 3)) { note(pk, 'S2A loop back-converted'); return s2aClauses(b0.a[0], pname, A.length, pk); }
      // DET wrapper:  copy_term(A, B), p__d(B.., S), p__dr(S, B.., A.., Rows)  -- the packet code is p__cpx
      if (gs.length === 3 && isC(b0, 'copy_term', 2) && D(gs[1]).t === 'c' && /__d$/.test(D(gs[1]).f) && D(gs[2]).t === 'c' && /__dr$/.test(D(gs[2]).f)) {
        note(pk, 'deterministic mode dropped (DET is an optimisation only)');
        const inner = getCls(pname + '__cpx/' + (A.length + 1));
        if (inner.length !== 1) throw BackError('DET packet predicate has several clauses');
        const ih = D(inner[0].head);
        return decompPacketClause({ head: Cmp(pname + '__cp', ih.a), body: inner[0].body }, pk, pname);
      }
      // MEMO wrapper
      if (gs.length === 2 && isC(b0, 'memo_lookup', 3)) {
        note(pk, 'memo table dropped (memoisation is an optimisation only)');
        const mk = P.key(gs[1]); const mcls = getCls(mk);
        const none = mcls.find(c => isA(D(c.head).a[0], 'none'));
        if (!none) throw BackError('memo wrapper without a none clause');
        const call = D(flat(none.body)[0]);
        const inner = getCls(P.key(call));
        if (inner.length !== 1) throw BackError('memo compute predicate has several clauses');
        return decompPacketClause(inner[0], pk, pname);
      }
      // PRED: clause packets then rows_concat
      const last = D(gs[gs.length - 1]);
      if ((isC(last, 'rows_concat', 2) || isC(last, 'rows_cut_concat', 2)) && D(last.a[1]) === D(Rows) && gs.length >= 2 && !isC(b0, 'copy_term', 2) && !isC(b0, 'if_commit', 3)) {
        const out = [];
        for (const g of gs.slice(0, -1)) {
          const cc = getCls(P.key(g)); if (cc.length !== 1) throw BackError('clause packet ' + P.key(g) + ' has several clauses');
          out.push(...decompClausePacket(cc[0], pname, pk));
        }
        return out;
      }
      // CLAUSE (single clause)
      return decompClausePacket(cl, pname, pk);
    }
    function s2aClauses(spec, pname, n, pk) {
      spec = D(spec); const K = D(spec.a[0]).v; const cols = listToArray(spec.a[1]).map(D);
      const allFormula = cols.every(c => c.f === 'newton' || c.f === 'const') && cols.some(c => c.f === 'newton');
      if (allFormula && K > 3) {
        const isId = c => c.f === 'newton' && listToArray(c.a[0]).map(x => D(x).v).join(',') === '0,1';
        const idj = cols.findIndex(isId);
        const I = idj >= 0 ? Var('A' + (idj + 1)) : Var('I'); const As = []; const goals = [Cmp('between', [Int(0), Int(K - 1), I])];
        cols.forEach((c, j) => {
          if (j === idj) { As.push(I); return; }
          const Aj = Var('A' + (j + 1)); As.push(Aj);
          if (c.f === 'const') goals.push(Cmp('=', [Aj, c.a[0]]));
          else goals.push(Cmp('is', [Aj, newtonExpr(listToArray(c.a[0]).map(x => D(x).v), I)]));
        });
        note(pk, 'S2A loop written as a formula over I = 0..' + (K - 1));
        return [{ head: Cmp(pname, As), body: conj(goals) }];
      }
      const out = [];
      for (let I = 0; I < K; I++) {
        const row = cols.map(c => c.f === 'const' ? c.a[0] : c.f === 'data' ? listToArray(c.a[0])[I] : Int(listToArray(c.a[0]).map(x => D(x).v).reduce((s, d, i) => s + d * P.binom(I, i), 0)));
        out.push({ head: Cmp(pname, row.map(x => copy(x))), body: P.TRUE });
      }
      note(pk, 'S2A loop written as its ' + K + ' facts (the original rules are replaced by their answer table)');
      return out;
    }
    function newtonExpr(ds, I) {
      const { c, den } = P.newtonPoly(ds);
      const mon = k => k === 1 ? I : k === 2 ? Cmp('*', [I, I]) : Cmp('*', [Cmp('*', [I, I]), I]);
      let e = null;
      for (let k = 3; k >= 0; k--) {
        if (!c[k]) continue;
        const a = Math.abs(c[k]);
        const t = k === 0 ? Int(a) : a === 1 ? mon(k) : Cmp('*', [Int(a), mon(k)]);
        if (e === null) e = c[k] < 0 ? (k === 0 ? Int(-a) : Cmp('-', [t])) : t;
        else e = Cmp(c[k] < 0 ? '-' : '+', [e, t]);
      }
      if (e === null) e = Int(0);
      return den === 1 ? e : Cmp('//', [e, Int(den)]);
    }
    // clause packet:  if_commit(copy_term(A, H), (Code, project_rows(R0, L, H, Rows)), Rows = [])
    //            or:  copy_term(A, H), Code, project_rows(R0, L, H, Rows)   (head arguments distinct variables)
    function decompClausePacket(cl, pname, pk) {
      const gs = flat(cl.body);
      let ren0, tg;
      // call-through:  h__cp(A.., Rows) :- q__cp(A.., Rows)
      { const h = D(cl.head); const g0 = D(gs[0]);
        if (gs.length === 1 && g0.t === 'c' && /__cp$/.test(g0.f) && g0.a.length === h.a.length && g0.a.every((x, i) => D(x) === D(h.a[i]))) {
          const vs = h.a.slice(0, -1).map((_, i) => Var('X' + (i + 1)));
          return [{ head: Cmp(pname, vs), body: Cmp(g0.f.replace(/__cp$/, ''), vs) }];
        } }
      if (gs.length === 1 && isC(gs[0], 'if_commit', 3) && isC(D(gs[0]).a[0], 'copy_term', 2)) { ren0 = D(D(gs[0]).a[0]); tg = flat(D(gs[0]).a[1]); }
      else if (gs.length >= 2 && isC(gs[0], 'copy_term', 2)) { ren0 = D(gs[0]); tg = gs.slice(1); }
      else throw BackError('unexpected clause packet ' + P.key(cl.head));
      const H = listToArray(ren0.a[1]);
      if (isC(tg[tg.length - 1], 'strip_cut', 2)) tg = tg.slice(0, -1);
      const pr = D(tg[tg.length - 1]);
      let R0, L, code;
      if (isC(pr, 'project_rows', 4)) { R0 = D(pr.a[0]); L = pr.a[1]; code = tg.slice(0, -1); }
      else { // identity projection: the environment is the head arguments and the code computes the packet itself
        const Rows = D(cl.head).a[D(cl.head).a.length - 1];
        if (!H.every(x => D(x).t === 'v')) throw BackError('clause packet without project_rows');
        R0 = D(Rows); L = list(H); code = tg;
      }
      const names = new Map();
      const ctx = { names, L, pk };
      const body = decompCode(code, R0, ctx);
      let clause = { head: Cmp(pname, H.map(x => ren(x, names))), body };
      const restored = restoreCuts(clause, pname, pk);
      return restored.map(c => cleanup(c, pk));
    }
    function ren(t, names) {
      t = D(t);
      if (t.t === 'v') {
        if (!t.name || t.name === '_') return Var('_');
        let v = names.get(t.name); if (!v) { v = Var(t.name); names.set(t.name, v); } return v;
      }
      if (t.t === 'c') return Cmp(t.f, t.a.map(x => ren(x, names)));
      return t;
    }

    // decompile a Detlog code sequence that computes packet O (in env L) into one Prolog goal
    function decompCode(gs, O, ctx) {
      gs = gs.map(D);
      if (!gs.length) throw BackError('empty code');
      const u = unit(gs, 0, ctx);
      let goal = u.goal; let i = u.next; let cur = u.out;
      while (i < gs.length) {
        const g = gs[i];
        // seq: nm(Cur, Next)
        if (g.t === 'c' && g.a.length === 2 && D(g.a[0]) === cur && isSeqAux(P.key(g))) {
          const rest = decompSeqAux(P.key(g), ctx);
          goal = conj([goal, rest]); cur = D(g.a[1]); i++; continue;
        }
        if (isC(g, '=', 2) && D(g.a[1]) === cur) { cur = D(g.a[0]); i++; continue; }
        throw BackError('unexpected goal ' + show(g, { varName: v => v.name || '_' }));
      }
      if (cur !== D(O)) throw BackError('code does not compute its output packet');
      return goal;
    }
    function isSeqAux(k) {
      const cls = prog.preds.get(k); if (!cls || cls.length !== 2) return false;
      return isA(D(cls[0].head).a[0], '[]');
    }
    function decompSeqAux(k, ctx) {
      const cls = getCls(k);
      const rk = P.key(flat(cls[1].body)[0]);
      const rcls = getCls(rk);
      const ecl = rcls.find(c => isC(D(c.head).a[0], 'e', 1));
      if (!ecl) throw BackError('row predicate ' + rk + ' without an e/1 clause');
      const gs = flat(ecl.body);
      if (!isC(gs[0], 'copy_term', 2)) throw BackError('row predicate without copy_term');
      return decompCode(gs.slice(1), D(ecl.head).a[1], ctx);
    }
    function auxBody(k, which, ctx) { // single-clause aux nm(e(L), O) :- Code
      const cls = getCls(k);
      const cl = which ? cls.find(which) : cls[0];
      if (!cl) throw BackError('missing clause of ' + k);
      const h = D(cl.head);
      return decompCode(flat(cl.body), h.a[h.a.length - 1], ctx);
    }

    // one unit: returns {goal, out, next}
    function unit(gs, i, ctx) {
      const g = gs[i]; const k = P.key(g);
      const r = x => ren(x, ctx.names);
      // O = [e(L)] / O = []
      if (isC(g, '=', 2)) {
        const rhs = D(g.a[1]);
        if (isA(rhs, '[]')) return { goal: P.FAIL, out: D(g.a[0]), next: i + 1 };
        const l = listToArray(rhs);
        if (l && l.length === 1 && isC(l[0], 'e', 1)) return { goal: P.TRUE, out: D(g.a[0]), next: i + 1 };
        if (l && l.length === 2 && isA(l[0], 'cut') && isC(l[1], 'e', 1)) return { goal: Atom('!'), out: D(g.a[0]), next: i + 1 };
        if (l && l.length === 2 && isC(l[0], 'out', 1)) throw BackError('out item without effect_text');
      }
      if (k === 'if_commit/3') {
        const C = D(g.a[0]), T = flat(g.a[1]), F = flat(g.a[2]);
        // det:  if_commit(B, O = [e(L)], O = [])
        const OT = outOfSimple(T), OF = outOfSimple(F);
        if (OT && OF && OT.v === OF.v && OT.kind === 'row' && OF.kind === 'none') return { goal: r(C), out: OT.v, next: i + 1 };
        // DET-call:  if_commit((q__d(As.., S), S \== maybe), if_commit(S = yes, ..), (q__cp(As.., P), splice_extend(..)))
        if (isC(C, ',', 2) && D(D(C).a[0]).t === 'c' && /__d$/.test(D(D(C).a[0]).f) && isC(D(C).a[1], '\\==', 2)) {
          const Os = findOut(F);
          return { goal: decompCode(F, Os, ctx), out: Os, next: i + 1 };
        }
        // splice:  if_commit(splice_safe(..), Chain, Seq)
        if (isC(C, 'splice_safe', 2)) {
          ctx.splice = true; note(ctx.pk, 'splice written back as the sequential conjunction');
          const Os = findOut(F);
          return { goal: decompCode(F, Os, ctx), out: Os, next: i + 1 };
        }
        // aggregate:  if_commit((aggregate_list(S, Ts, R), Target = R), rows_concat([Outs,[e(L)]], O), O = Outs)
        if (isC(C, ',', 2) && isC(D(C).a[0], 'aggregate_list', 3)) throw BackError('aggregate outside findall template');
        // det_prefix:  if_commit(B, Code(O), O = [])
        if (OF && OF.kind === 'none') {
          const inner = decompCode(T, OF.v, ctx);
          return { goal: conj([r(C), inner]), out: OF.v, next: i + 1 };
        }
        // ite_det:  if_commit(C, CodeT(O), CodeF(O))
        const Ot = findOut(T), Of = findOut(F);
        if (Ot && Of && Ot === Of) {
          const tg = decompCode(T, Ot, ctx), fg = decompCode(F, Of, ctx);
          // a scan with a deterministic prefix:  if_commit(Pre, q(Xs, e(L), O), CodeF(O))
          const tc = D(tg);
          const isScan = (T.length === 1 && scanOf(P.key(T[0]), ctx)) || (T.length === 2 && D(T[0]).t === 'c' && /__rows$/.test(D(T[0]).f) && scanOf(P.key(T[1]), ctx, D(T[0]).f.replace(/__rows$/, '')));
          if (isScan && tc.t === 'c' && tc.f === ';' && isC(tc.a[0], '->', 2) && show(tc.a[1]) === show(fg))
            return { goal: mkIte(conj([r(C), D(tc.a[0]).a[0]]), D(tc.a[0]).a[1], fg), out: Ot, next: i + 1 };
          return { goal: mkIte(r(C), tg, fg), out: Ot, next: i + 1 };
        }
        throw BackError('unrecognised if_commit/3');
      }
      if (k === 'effect_text/2') {
        const nx = gs[i + 1];
        if (isC(nx, '=', 2)) {
          const rhs = D(nx.a[1]); const l = listToArray(rhs);
          if (l && l.length === 2 && isC(l[0], 'out', 1)) return { goal: r(g.a[0]), out: D(nx.a[0]), next: i + 2 };
          // effect_prefix:  effect_text(B, T), Code(O1), O = [out(T)|O1]
        }
        // find O = [out(T)|O1]
        for (let j = i + 1; j < gs.length; j++) {
          const q = gs[j];
          if (isC(q, '=', 2) && isC(q.a[1], '.', 2) && isC(D(q.a[1]).a[0], 'out', 1) && D(D(D(q.a[1]).a[0]).a[0]) === D(g.a[1])) {
            const O1 = D(D(q.a[1]).a[1]);
            const rest = decompCode(gs.slice(i + 1, j), O1, ctx);
            return { goal: conj([r(g.a[0]), rest]), out: D(q.a[0]), next: j + 1 };
          }
        }
        throw BackError('effect_text without its out item');
      }
      if (k === 'builtin_rows/2') {
        const nx = gs[i + 1];
        if (!isC(nx, 'splice_extend', 4)) throw BackError('builtin_rows without splice_extend');
        return { goal: r(g.a[0]), out: D(nx.a[3]), next: i + 2 };
      }
      if (k === 'copy_term/2') {
        const a0 = D(g.a[0]);
        // findall / aggregate:  copy_term(f(e(L),T), f(EG,TG)), nm(EG,RG), packet_split, project_list, if_commit
        if (isC(a0, 'f', 2)) {
          const call = gs[i + 1], split = gs[i + 2], proj = gs[i + 3], fin = D(gs[i + 4]);
          if (!call || !isC(split, 'packet_split', 3) || !isC(proj, 'project_list', 4) || !isC(fin, 'if_commit', 3)) throw BackError('unrecognised findall pattern');
          const G = auxBody(P.key(call), null, ctx);
          const Tm = r(a0.a[1]);
          const out = findOut(flat(fin.a[1]));
          const cnd = D(fin.a[0]);
          if (isC(cnd, ',', 2) && isC(D(cnd.a[0]), 'aggregate_list', 3)) {
            const sp = D(D(cnd.a[0]).a[0]).n; const target = r(D(cnd.a[1]).a[0]);
            const spec = sp === 'count' ? Atom('count') : Cmp(sp, [Tm]);
            return { goal: Cmp('aggregate_all', [spec, G, target]), out, next: i + 5 };
          }
          return { goal: Cmp('findall', [Tm, G, r(D(cnd).a[0])]), out, next: i + 5 };
        }
        // disjunction:  copy_term(e(L),E1), d1(E1,R1), ..., rows_concat([R1..], O)
        // if-then-else: copy_term(e(L),EC), k(EC,RC), packet_first(RC,Pre,First), i(First,e(L),RB), rows_concat([Pre,RB],O)
        const call = gs[i + 1]; const nx2 = gs[i + 2];
        if (isC(nx2, 'packet_first', 3)) {
          const ic = gs[i + 3], rc = gs[i + 4];
          const Cg = auxBody(P.key(call), null, ctx);
          const ik = P.key(ic);
          const Fg = auxBody(ik, c => isA(D(c.head).a[0], '[]'), ctx);
          const Tg = auxBody(ik, c => isC(D(c.head).a[0], '.', 2), ctx);
          return { goal: mkIte(Cg, Tg, Fg), out: D(D(rc).a[1]), next: i + 5 };
        }
        // disjunction
        const alts = []; let j = i;
        while (j < gs.length && isC(gs[j], 'copy_term', 2) && isC(D(gs[j]).a[0], 'e', 1)) {
          alts.push(auxBody(P.key(gs[j + 1]), null, ctx)); j += 2;
        }
        const rc = gs[j];
        if (!isC(rc, 'rows_concat', 2) && !isC(rc, 'rows_concat_cut', 2)) throw BackError('unrecognised disjunction');
        let dg = alts[alts.length - 1]; for (let q = alts.length - 2; q >= 0; q--) dg = Cmp(';', [alts[q], dg]);
        return { goal: dg, out: D(D(rc).a[1]), next: j + 1 };
      }
      // facts scan:  p__rows(T), q(T, e(L), O)
      if (g.t === 'c' && g.a.length === 1 && /__rows$/.test(g.f) && gs[i + 1] && D(gs[i + 1]).t === 'c' && D(D(gs[i + 1]).a[0]) === D(g.a[0])) {
        const q = D(gs[i + 1]); const sc = scanOf(P.key(q), ctx, g.f.replace(/__rows$/, ''));
        if (sc) return { goal: mkIte(conj([sc.gen, sc.post]), sc.T, sc.F), out: D(q.a[2]), next: i + 2 };
      }
      // first-match scan:  q(Xs, e(L), O)
      if (g.t === 'c' && g.a.length === 3 && isC(g.a[1], 'e', 1)) {
        const sc = scanOf(P.key(g), ctx);
        if (sc) return { goal: mkIte(conj([Cmp('member', [sc.X, r(g.a[0])]), sc.post]), sc.T, sc.F), out: D(g.a[2]), next: i + 1 };
      }
      // user call:  q__cp(Args, P), splice_extend(P, Args, e(L), O)
      if (g.t === 'c' && /__cp$/.test(g.f)) {
        const nx = gs[i + 1];
        if (!isC(nx, 'splice_extend', 4)) throw BackError('call without splice_extend');
        const nm = g.f.replace(/__cp$/, '');
        return { goal: Cmp(nm, g.a.slice(0, -1).map(r)), out: D(nx.a[3]), next: i + 2 };
      }
      throw BackError('unrecognised goal ' + show(g, { varName: v => v.name || '_' }));
    }
    // nm(Xs, e(L), O) :- if_commit(Xs = [Y|Ys], if_commit((X = Y, Post), T, nm(Ys, e(L), O)), F)
    function scanOf(k, ctx, factsName) {
      const cls = prog.preds.get(k); if (!cls || cls.length !== 1) return null;
      const h = D(cls[0].head); const b = D(cls[0].body);
      if (!isC(b, 'if_commit', 3)) return null;
      const c1 = D(b.a[0]), inner = D(b.a[1]);
      if (!isC(c1, '=', 2) || D(c1.a[0]) !== D(h.a[0]) || !isC(c1.a[1], '.', 2) || !isC(inner, 'if_commit', 3)) return null;
      const Y = D(D(c1.a[1]).a[0]), Ys = D(D(c1.a[1]).a[1]);
      const cg = flat(inner.a[0]); const first = D(cg[0]);
      const rec = flat(inner.a[2]); if (rec.length !== 1 || P.key(rec[0]) !== k || D(D(rec[0]).a[0]) !== Ys) return null;
      const r = x => ren(x, ctx.names); const O = h.a[2];
      if (factsName) {
        if (!isC(first, 'copy_term', 2) || D(first.a[0]) !== Y) return null;
        return { gen: Cmp(factsName, listToArray(first.a[1]).map(r)), post: conj(cg.slice(1).map(r)), T: decompCode(flat(inner.a[1]), O, ctx), F: decompCode(flat(b.a[2]), O, ctx) };
      }
      if (!isC(first, '=', 2) || D(first.a[1]) !== Y) return null;
      return { X: r(first.a[0]), post: conj(cg.slice(1).map(r)), T: decompCode(flat(inner.a[1]), O, ctx), F: decompCode(flat(b.a[2]), O, ctx) };
    }
    function outOfSimple(gs) {
      if (gs.length !== 1) return null; const g = D(gs[0]);
      if (!isC(g, '=', 2)) return null; const rhs = D(g.a[1]);
      if (isA(rhs, '[]')) return { v: D(g.a[0]), kind: 'none' };
      const l = listToArray(rhs); if (l && l.length === 1 && isC(l[0], 'e', 1)) return { v: D(g.a[0]), kind: 'row' };
      return null;
    }
    // the variable a code sequence binds as its packet (its last output)
    function findOut(gs) {
      const g = D(gs[gs.length - 1]);
      if (isC(g, '=', 2)) return D(g.a[0]);
      if (isC(g, 'if_commit', 3)) { const t = flat(g.a[2]); return findOut(t); }
      if (isC(g, 'rows_concat', 2) || isC(g, 'rows_concat_cut', 2)) return D(g.a[1]);
      if (isC(g, 'splice_extend', 4)) return D(g.a[3]);
      if (g.t === 'c' && g.a.length >= 2) return D(g.a[g.a.length - 1]);
      return null;
    }
    function mkIte(C, T, F) {
      if (isA(T, 'fail') && isA(F, 'true')) return Cmp('\\+', [C]);
      if (isA(T, 'true') && isA(F, 'fail')) return Cmp('once', [C]);
      if (isA(T, 'true') && isA(F, 'true')) return Cmp('ignore', [C]);
      return Cmp(';', [Cmp('->', [C, T]), F]);
    }

    // rule CUT inverse: p(H..) :- ( [H..]=[h..], G -> B ; Rest )  ==>  p(h..) :- G, !, B.  + Rest
    function restoreCuts(clause, pname, pk) {
      const h = D(clause.head); const H = h.t === 'c' ? h.a.map(D) : [];
      const isMergedHead = H.length > 0 && H.every(v => v.t === 'v' && /^[HA]__\d+$/.test(v.name || '')) || (H.length === 0 && /__c\d/.test(show(clause.body, { varName: v => v.name || '_' })));
      if (!isMergedHead) return [clause];
      const out = [];
      let b = D(clause.body);
      const headEq = g => { g = D(g); if (H.length === 0) return { ok: true, args: [], rest: g }; const gs = flat(g); const e0 = D(gs[0]); if (isC(e0, '=', 2) && listToArray(e0.a[0]) && listToArray(e0.a[0]).every((x, i) => D(x) === H[i])) return { ok: true, args: listToArray(e0.a[1]), rest: conj(gs.slice(1)) }; return { ok: false }; };
      for (;;) {
        if (isA(b, 'fail')) break;
        if (isC(b, ';', 2) && isC(D(b).a[0], '->', 2)) {
          const it = D(D(b).a[0]); const he = headEq(it.a[0]);
          if (!he.ok) return [clause];
          out.push({ head: Cmp(pname, he.args), body: conj([he.rest, Atom('!'), restoreLaterCuts(it.a[1])]) });
          b = D(D(b).a[1]); continue;
        }
        if (isC(b, 'once', 1)) { const he = headEq(D(b).a[0]); if (!he.ok) return [clause]; out.push({ head: Cmp(pname, he.args), body: conj([he.rest, Atom('!')]) }); break; }
        if (isC(b, ';', 2)) {
          const he = headEq(D(b).a[0]); if (!he.ok) return [clause];
          out.push({ head: Cmp(pname, he.args), body: he.rest }); b = D(D(b).a[1]); continue;
        }
        const he = headEq(b); if (!he.ok) return [clause];
        out.push({ head: Cmp(pname, he.args), body: he.rest }); break;
      }
      note(pk, 'cuts restored from the if_commit chain (rule CUT)');
      return out;
    }
    function restoreLaterCuts(g) {
      g = D(g);
      if (isC(g, ';', 2) && isC(D(g).a[0], '->', 2) && isA(D(g).a[1], 'fail')) { const it = D(D(g).a[0]); return conj([it.a[0], Atom('!'), restoreLaterCuts(it.a[1])]); }
      if (isC(g, 'once', 1)) return conj([g.a[0], Atom('!')]);
      return g;
    }
    // variable names: strip generated suffixes, anonymous singletons back to _
    function cleanup(c, pk) {
      const t = Cmp(':-', [c.head, c.body]);
      const counts = new Map();
      (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(t);
      const used = new Set();
      for (const v of counts.keys()) {
        let nm = v.name || '_';
        nm = nm.replace(/__c\d+$/, '');
        if (/^U__\d+$/.test(nm)) nm = counts.get(v) === 1 ? '_' : '_U' + nm.slice(3);
        else if (/^U__/.test(nm)) nm = '_' + nm.slice(3);
        else if (/^H__(\d+)$/.test(nm)) nm = 'H' + nm.slice(3);
        else if (/^L__[fb]$/.test(nm)) nm = 'L_';
        if (nm !== '_') { let base = nm, j = 2; while (used.has(nm)) nm = base + '_' + (j++); used.add(nm); }
        v.name = nm;
      }
      return { head: c.head, body: simplify(c.body) };
    }
    function simplify(g) {
      g = D(g);
      if (isC(g, ',', 2)) return conj(flat(g).map(simplify));
      if (isC(g, ';', 2)) { const a = simplify(g.a[0]), b = simplify(g.a[1]); if (isA(b, 'fail') && !isC(a, '->', 2)) return a; return Cmp(';', [a, b]); }
      if (isC(g, '->', 2)) return Cmp('->', [simplify(g.a[0]), simplify(g.a[1])]);
      if (isC(g, '\\+', 1)) {
        // \+ (C, \+ A)  ==>  forall(C, A)
        const inner = D(g.a[0]);
        if (isC(inner, ',', 2) && isC(D(inner.a[1]), '\\+', 1)) return Cmp('forall', [simplify(inner.a[0]), simplify(D(inner.a[1]).a[0])]);
        return Cmp('\\+', [simplify(g.a[0])]);
      }
      if (isC(g, 'findall', 3)) return Cmp('findall', [g.a[0], simplify(g.a[1]), g.a[2]]);
      return g;
    }

    // ---- fold specialised higher-order predicates back into maplist/foldl ----
    const specRe = /^(maplist|foldl|include|exclude|partition)_\w*__s\d+$/;
    const folded = new Map();
    for (const [pk, cls] of predClauses) {
      const nm = pk.slice(0, pk.lastIndexOf('/'));
      const m = specRe.exec(nm);
      if (!m || !cls || cls.length !== 2) continue;
      const kind = m[1];
      const c2 = cls[1]; const h2 = D(c2.head); const bg = flat(c2.body);
      const nL = h2.a.filter(x => isC(x, '.', 2)).length;
      let g0 = D(bg[0]); let extra, nListArgs, fvStart;
      if (kind === 'maplist') { extra = nL; nListArgs = nL; fvStart = nL; }
      else if (kind === 'foldl') { extra = nL + 2; nListArgs = nL + 2; fvStart = nL + 2; }
      else { // include/exclude/partition: ( G(X) -> ... ; ... )
        if (!(isC(g0, ';', 2) && isC(D(g0.a[0]), '->', 2))) continue;
        g0 = D(D(g0.a[0]).a[0]); extra = 1; nListArgs = kind === 'partition' ? 3 : 2; fvStart = nListArgs;
      }
      const fv = h2.a.slice(fvStart).map(D);
      let clo;
      if (/_lambda__s\d+$/.test(nm)) {
        // lambda: parameters are the list elements, body is every goal before the recursive call
        const elems = h2.a.slice(0, nL).map(x => D(x).a[0]);
        if (kind === 'foldl') elems.push(h2.a[nL], null);
        const bodyGoals = kind === 'maplist' || kind === 'foldl' ? bg.slice(0, -1) : [g0];
        let ps = elems.filter(Boolean);
        if (kind === 'foldl') { const nx = D(bg[bg.length - 1]).a[nL]; ps = h2.a.slice(0, nL).map(x => D(x).a[0]).concat([h2.a[nL], nx]); }
        clo = Cmp('>>', [list(ps), conj(bodyGoals)]);
      } else {
        if (g0.t !== 'c' && g0.t !== 'a') continue;
        const gargs = g0.t === 'c' ? g0.a : [];
        clo = gargs.length - extra === 0 ? Atom(P.name(g0)) : Cmp(P.name(g0), gargs.slice(0, gargs.length - extra));
      }
      folded.set(pk, { kind, arity: nListArgs + 1, clo, fv, nListArgs });
    }
    function foldCalls(g) {
      g = D(g);
      if (g.t === 'c' && [',', ';', '->', '\\+', 'findall', 'forall', 'once', 'ignore', 'aggregate_all'].includes(g.f)) return Cmp(g.f, g.a.map((x, i) => (g.f === 'findall' || g.f === 'aggregate_all') && i !== 1 ? x : foldCalls(x)));
      const k = P.key(g); const fi = folded.get(k);
      if (!fi) return g;
      const lists = g.a.slice(0, fi.nListArgs);
      const fvArgs = g.a.slice(lists.length);
      // substitute the spec's closure variables with the call's arguments
      const map = new Map(); fi.fv.forEach((v, i) => { if (v.t === 'v') map.set(v, fvArgs[i]); });
      const clo = subst(fi.clo, map);
      return Cmp(fi.kind, [clo].concat(lists));
    }
    function subst(t, map) { t = D(t); if (t.t === 'v') return map.has(t) ? map.get(t) : t; if (t.t === 'c') return Cmp(t.f, t.a.map(x => subst(x, map))); return t; }
    if (folded.size) {
      for (const [pk, cls] of predClauses) if (cls) for (const c of cls) c.body = foldCalls(c.body);
      for (const pk of folded.keys()) { res.notes.push('specialised ' + pk + ' folded back into ' + folded.get(pk).kind + '/' + folded.get(pk).arity); predClauses.delete(pk); }
    }

    // ---- assemble ----
    const lines = ['% Prolog back-converted from Detlog by pl2detlog.'];
    for (const [pk, cls] of predClauses) {
      if (/^\$query\d+\//.test(pk)) { if (cls && cls[0]) res.queries.push({ pred: pk, goal: P.show(cls[0].body, { varName: v => v.name }) }); continue; }
      res.preds.push({ key: pk, clauses: cls, notes: predNotes.get(pk) || [] });
      if (!cls) { lines.push('', '% ' + pk + ': not back-convertible'); continue; }
      lines.push('');
      for (const n of predNotes.get(pk) || []) lines.push('% ' + pk + ': ' + n);
      for (const c of cls) { const t = isA(c.body, 'true') ? c.head : Cmp(':-', [c.head, c.body]); lines.push(P.showClause(t, { varName: v => v.name && v.name !== '_' ? v.name : '_' })); res.clauses.push(t); }
    }
    res.text = lines.join('\n') + '\n';
    return res;
  }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }

  // ---- change warnings: compare back-converted Prolog with the original source, predicate by predicate ----
  function normText(src) {
    const prog = P.loadProgram(src); const m = new Map();
    for (const k of prog.order) {
      m.set(k, prog.preds.get(k).map(cl => {
        const mp = new Map(); const c = copy(Cmp(':-', [cl.head, cl.body]), mp);
        if (cl.vars) for (const [nm, v] of cl.vars) { const nv = mp.get(v); if (nv) nv.name = nm; }
        return canon(c);
      }));
    }
    return m;
  }
  // canonical text with variables numbered in order of appearance (names do not matter)
  function canon(t) { const nm = P.namer(); const b = D(t.a[1]); return isA(b, 'true') ? P.show(t.a[0], { varName: nm }) : P.show(t, { varName: nm }); }
  function changeWarnings(originalSrc, backText, backRes) {
    const o = normText(originalSrc), b = normText(backText);
    const warnings = [];
    for (const [k, ocls] of o) {
      const bcls = b.get(k);
      const notes = (backRes && (backRes.preds.find(p => p.key === k) || {}).notes) || [];
      if (!bcls) { const nb = backRes && backRes.preds.find(p => p.key === k); warnings.push({ pred: k, kind: nb && !nb.clauses ? 'error' : 'removed', msg: nb && !nb.clauses ? 'not back-convertible' : 'predicate is missing from the back-converted program', notes }); continue; }
      if (ocls.length === bcls.length && ocls.every((c, i) => c === bcls[i])) { warnings.push({ pred: k, kind: 'same', msg: 'unchanged', notes }); continue; }
      const diff = [];
      const n = Math.max(ocls.length, bcls.length);
      for (let i = 0; i < n; i++) if (ocls[i] !== bcls[i]) diff.push({ i: i + 1, was: ocls[i] || null, now: bcls[i] || null });
      warnings.push({ pred: k, kind: 'changed', msg: describeChange(ocls, bcls, notes), diff, notes });
    }
    for (const [k] of b) if (!o.has(k)) warnings.push({ pred: k, kind: 'added', msg: 'predicate added (not in the original source)', notes: [] });
    return warnings;
  }
  function describeChange(o, b, notes) {
    if (notes.some(n => /S2A/.test(n))) return 'rules replaced by their S2A answer table / formula (same answers for every call that raises no error)';
    const ot = o.join(' '), bt = b.join(' ');
    const reasons = [];
    if (/\bonce\(|\bignore\(|\bforall\(|\bcall\(/.test(ot) && !/\bonce\(|\bignore\(|\bforall\(|\bcall\(/.test(bt)) reasons.push('once/ignore/forall/call written as if-then-else');
    if (/\bnot\(/.test(ot)) reasons.push('not/1 written as \\+');
    if (/\bbagof\(|\bsetof\(/.test(ot)) reasons.push('bagof/setof written as findall');
    if (/\bphrase\(/.test(ot) && !/\bphrase\(/.test(bt)) reasons.push('phrase/2,3 written as a direct DCG call');
    if ((ot.match(/!/g) || []).length !== (bt.match(/!/g) || []).length) reasons.push('cut placement written as an if-then-else');
    if (/->/.test(bt) && !/->/.test(ot)) reasons.push('local cut written as an if-then-else');
    if (o.length !== b.length) reasons.push('number of clauses changed (' + o.length + ' -> ' + b.length + ')');
    return (reasons.length ? reasons.join('; ') : 'clause text changed') + ' — equivalence is checked by evaluation';
  }

  P.backConvert = backConvert; P.changeWarnings = changeWarnings; P.canonClauses = normText;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
