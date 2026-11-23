/* pl2detlog converter: Prolog with cuts and choicepoints -> cut-free, choicepoint-free Detlog.
   Every goal denotes an answer packet: a list of e(EnvRow) rows and out(Text) items, in Prolog order.
   findall/aggregate_all/\+/if-then-else/once are written as packet predicates; the output contains no
   cut, ;, ->, \+, findall, call/N or nondeterministic builtin.  Each rewrite is recorded as a proof step. */
(function (P) {
  'use strict';
  const { Atom, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, listToArray, copy, termVars, show } = P;
  const D = deref;
  const conj = gs => { gs = gs.filter(g => !(D(g).t === 'a' && D(g).n === 'true')); if (!gs.length) return P.TRUE; let r = gs[gs.length - 1]; for (let i = gs.length - 2; i >= 0; i--) r = Cmp(',', [gs[i], r]); return r; };
  const flatConj = (g, out) => { out = out || []; g = D(g); if (g.t === 'c' && g.f === ',' && g.a.length === 2) { flatConj(g.a[0], out); flatConj(g.a[1], out); } else out.push(g); return out; };
  const flatDisj = (g, out) => { out = out || []; g = D(g); if (g.t === 'c' && g.f === ';' && g.a.length === 2 && !isIte(g.a[0])) { out.push(g.a[0]); flatDisj(g.a[1], out); } else out.push(g); return out; };
  function isIte(g) { g = D(g); return g.t === 'c' && g.f === '->' && g.a.length === 2; }
  const kk = g => P.key(g);
  const eq = (a, b) => Cmp('=', [a, b]);
  const E = L => Cmp('e', [L]);

  // ----- builtin classification -----
  const EFFECT = new Set(['write/1', 'print/1', 'writeln/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'flush_output/0']);
  const DBEFFECT = new Set(['assert/1', 'asserta/1', 'assertz/1', 'retractall/1', 'nb_setval/2', 'b_setval/2', 'setarg/3', 'nb_setarg/3']);
  const NONDET_BI = new Set(['member/2', 'between/3', 'append/3', 'length/2', 'nth0/3', 'nth1/3', 'select/3', 'permutation/2', 'atom_concat/3', 'sub_atom/5', 'sub_string/5', 'arg/3', 'last/2', 'char_type/2', 'retract/1', 'get_dict/3', 'clause/2', 'current_prolog_flag/2', 'string_concat/3']);
  const GENERATOR_BI = new Set(['member/2', 'between/3']);
  const PURE_BI = new Set(['=/2', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2', 'between/3', 'member/2', 'succ/2', 'plus/3', 'true/0']);
  const CONTROL = new Set([',/2', ';/2', '->/2', '\\+/1', 'findall/3', 'findall/4', 'aggregate_all/3', 'bagof/3', 'setof/3', 'true/0', 'fail/0', 'false/0', '!/0']);
  function biKind(k, g) {
    if (k === 'format/3') { const s = D(D(g).a[0]); if (s.t === 'c' && ['atom', 'string', 'codes', 'chars'].includes(s.f) && s.a.length === 1) return 'det'; return 'effect'; }
    if (EFFECT.has(k)) return 'effect';
    if (DBEFFECT.has(k)) return 'dbeffect';
    if (NONDET_BI.has(k)) return 'nondet';
    const b = P.builtins[k];
    if (b && !b.nondet && !b.call) return 'det';
    return null;
  }
  P.biKind = biKind; P.EFFECT = EFFECT; P.NONDET_BI = NONDET_BI; P.PURE_BI = PURE_BI;

  // ----- naming -----
  function cpName(f) { return f + '__cp'; }

  // ===================== conversion =====================
  // opts: { mnn: bool, s2aMax: 1000, memo: bool, splice: bool, fuse: bool, s2a: bool }
  function convert(src, opts) {
    opts = Object.assign({ mnn: false, s2aMax: 1000 }, opts || {});
    const mnn = !!opts.mnn;
    const feat = { fuse: opts.fuse !== false, // det_prefix, effect_prefix, ite_det, neg_det are detlog2's standard goal rules (plain and MNN)
      scan: opts.scan !== false, // ite_scan/neg_scan: a committed member/2 condition is a first-match scan (plain and MNN)
      factScan: mnn && opts.scan !== false, // ite_scan over a predicate of facts (MNN)
      det: mnn && opts.det !== false, // DET: output-free predicates with first-argument-exclusive clauses run without packets
      splice: mnn && opts.splice !== false, s2a: mnn && opts.s2a !== false, memo: mnn && opts.memo !== false };
    // MNN: the source rewrites first (src/rewrite.js: solve for the last generator, accumulate an appended
    // result), each derived from first principles; their derivations are in out.algebra
    let algebra = [];
    if (mnn && opts.algebra !== false && typeof src === 'string' && P.rewrite) { const rw = P.rewrite(src); src = rw.text; algebra = rw.steps; }
    const prog = typeof src === 'string' ? P.loadProgram(src) : src;
    const out = { source: src, algebra, mode: mnn ? 'mnn' : 'plain', preds: [], clauses: [], steps: [], warnings: [], errors: [], report: [], feat, specs: [], queries: [] };
    // queries become predicates '$query<i>'(V1..Vk) so that they are converted like any clause body
    const queryPreds = new Set();
    (opts.queries || []).forEach((qt, i) => {
      try {
        const q = P.readTerm(qt);
        if (mnn && opts.algebra !== false && P.fuseQuery) q.term = P.fuseQuery(prog, q.term, algebra);
        const vars = q.vars.filter(([nm]) => !nm.startsWith('_'));
        const nm = '$query' + (i + 1);
        const head = Cmp(nm, vars.map(([, v]) => v));
        const cl = prog.add(Cmp(':-', [head, q.term]), q.vars);
        queryPreds.add(nm + '/' + vars.length);
        out.queries.push({ text: qt, pred: nm, vars: vars.map(([n]) => n), key: nm + '/' + vars.length });
      } catch (e) { out.queries.push({ text: qt, error: e.message }); }
    });
    out.queryPreds = queryPreds;
    const step = (rule, pred, srcTxt, info) => { const s = { id: out.steps.length + 1, rule, pred, src: srcTxt, clauses: [], info: info || {} }; out.steps.push(s); return s; };
    const userPreds = new Set(prog.order);

    // ---- 0. normalise clauses (names, higher-order specialisation, local cuts) ----
    const specs = new Map(); // variant key -> spec pred name
    const srcPreds = new Map(); // key -> [{head, body}]
    const order = [];
    const addSrc = (k, cl) => { if (!srcPreds.has(k)) { srcPreds.set(k, []); order.push(k); } srcPreds.get(k).push(cl); };
    let specN = 0;
    function renameVars(term) {
      const vs = termVars(term); let u = 0;
      const used = new Set(vs.map(v => v.name).filter(Boolean));
      for (const v of vs) {
        if (!v.name || v.name === '_') { v.name = 'U__' + (++u); continue; }
        if (v.name.startsWith('_')) { v.name = 'U__' + v.name.slice(1); continue; }
        if (v.name.includes('__')) { const nn = v.name.replace(/__+/g, '_'); out.warnings.push({ pred: null, msg: 'variable ' + v.name + ' renamed to ' + nn + ' (`__` is reserved for generated names)' }); v.name = nn; }
      }
      return term;
    }
    function normGoal(g, ctx) {
      g = D(g);
      if (g.t === 'v') throw convErr(ctx, 'call of an unbound variable goal (call/1 of a variable) needs call/N, which Detlog does not have');
      if (g.t === 'n' || g.t === 's') throw convErr(ctx, 'goal is not callable: ' + show(g));
      const k = kk(g);
      switch (k) {
        case ',/2': return Cmp(',', [normGoal(g.a[0], ctx), normGoal(g.a[1], ctx)]);
        case ';/2': {
          const l = D(g.a[0]);
          if (l.t === 'c' && l.f === '->' && l.a.length === 2) return Cmp(';', [Cmp('->', [cutLocal(normGoal(l.a[0], ctx), ctx), normGoal(l.a[1], ctx)]), normGoal(g.a[1], ctx)]);
          if (l.t === 'c' && l.f === '*->') throw convErr(ctx, 'soft-cut *-> is not supported');
          return Cmp(';', [normGoal(g.a[0], ctx), normGoal(g.a[1], ctx)]);
        }
        case '->/2': return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), normGoal(g.a[1], ctx)]), P.FAIL]);
        case '*->/2': throw convErr(ctx, 'soft-cut *-> is not supported');
        case '\\+/1': case 'not/1': rw(ctx, 'neg', g); return Cmp('\\+', [cutLocal(normGoal(g.a[0], ctx), ctx)]);
        case 'once/1': rw(ctx, 'once', g); return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), P.TRUE]), P.FAIL]);
        case 'ignore/1': rw(ctx, 'ignore', g); return Cmp(';', [Cmp('->', [cutLocal(normGoal(g.a[0], ctx), ctx), P.TRUE]), P.TRUE]);
        case 'forall/2': rw(ctx, 'forall', g); return Cmp('\\+', [Cmp(',', [cutLocal(normGoal(g.a[0], ctx), ctx), Cmp('\\+', [cutLocal(normGoal(g.a[1], ctx), ctx)])])]);
        case 'call/1': { const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'call/1 of an unbound variable'); rw(ctx, 'call', g); return cutLocal(normGoal(c, ctx), ctx); }
        case 'findall/3': return Cmp('findall', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), g.a[2]]);
        case 'findall/4': return Cmp(',', [Cmp('findall', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), Var('L__f')]), Cmp('append', [Var('L__f'), g.a[3], g.a[2]])]);
        case 'aggregate_all/3': return Cmp('aggregate_all', [g.a[0], cutLocal(normGoal(g.a[1], ctx), ctx), g.a[2]]);
        case 'bagof/3': case 'setof/3': {
          let gl = D(g.a[1]); const ex = [];
          while (gl.t === 'c' && gl.f === '^' && gl.a.length === 2) { termVars(gl.a[0], ex); gl = D(gl.a[1]); }
          const exS = new Set(termVars(g.a[0]).concat(ex));
          const free = termVars(gl).filter(v => !exS.has(v));
          const usedElsewhere = free.filter(v => ctx.otherVars && ctx.otherVars.has(v));
          if (usedElsewhere.length) throw convErr(ctx, g.f + '/3 groups by its free variables (' + usedElsewhere.map(v => v.name).join(', ') + '); add ^ or use findall/3');
          rw(ctx, g.f, g);
          const Lv = Var('L__b'); const goals = [Cmp('findall', [g.a[0], cutLocal(normGoal(gl, ctx), ctx), Lv]), Cmp('\\=', [Lv, NIL])];
          if (g.f === 'setof') goals.push(Cmp('sort', [Lv, g.a[2]])); else goals.push(eq(Lv, g.a[2]));
          return conj(goals);
        }
        case 'phrase/2': case 'phrase/3': { const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'phrase/2 of an unbound body needs call/N'); rw(ctx, 'phrase', g); return normGoal(addArgs(c, [g.a[1], g.a.length === 3 ? g.a[2] : NIL]), ctx); }
        case 'catch/3': ctx.warn('catch/3: errors are not caught in Detlog; the goal is converted on its own'); return normGoal(g.a[0], ctx);
      }
      if (k && k.startsWith('call/') && g.a.length > 1) {
        const c = D(g.a[0]); if (c.t === 'v') throw convErr(ctx, 'call/N with an unbound closure needs call/N, which Detlog does not have');
        rw(ctx, 'call', g); return normGoal(addArgs(c, g.a.slice(1)), ctx);
      }
      const hk = higherOrder(g, ctx); if (hk) return hk;
      if (k === '!/0') return g;
      if (!userPreds.has(k) && !specs.has(k) && !CONTROL.has(k) && !biKind(k, g) && !srcPreds.has(k)) {
        if (prog.dynamic.has(k)) return g;
        throw convErr(ctx, 'unknown procedure ' + k);
      }
      return g;
    }
    function rw(ctx, kind, g) { ctx.rewrites.push({ kind, src: show(g) }); }
    function addArgs(c, extra) { c = D(c); if (c.t === 'a') return Cmp(c.n, extra); if (c.t === 'c' && c.f === '>>' && c.a.length === 2) return applyLambda(c, extra); return Cmp(c.f, c.a.concat(extra)); }
    // yall lambda  Params>>Body  applied to arguments: parameters are substituted (variables) or unified (patterns)
    function applyLambda(c, extra) {
      let params = D(c.a[0]); let body = c.a[1];
      if (params.t === 'c' && params.f === '/' && params.a.length === 2) params = D(params.a[1]);
      const ps = listToArray(params) || [];
      const map = new Map(); const goals = [];
      ps.forEach((p, i) => { if (i >= extra.length) return; const pd = D(p); if (pd.t === 'v' && !map.has(pd)) map.set(pd, extra[i]); else goals.push(eq(p, extra[i])); });
      const sub = t => { t = D(t); if (t.t === 'v') return map.has(t) ? map.get(t) : t; if (t.t === 'c') return Cmp(t.f, t.a.map(sub)); return t; };
      let g = sub(body);
      if (extra.length > ps.length) g = addArgs(g, extra.slice(ps.length));
      return conj(goals.map(sub).concat([g]));
    }
    // maplist/foldl/include/exclude/partition with a known closure -> specialised predicate (rule SPEC)
    function higherOrder(g, ctx) {
      const k = kk(g); const m = /^(maplist|foldl|include|exclude|partition)\/(\d)$/.exec(k);
      if (!m) return null;
      const kind = m[1], ar = +m[2];
      if (kind === 'maplist' && (ar < 2 || ar > 7)) return null;
      if (kind === 'foldl' && (ar < 4 || ar > 6)) return null;
      if ((kind === 'include' || kind === 'exclude') && ar !== 3) return null;
      if (kind === 'partition' && ar !== 4) return null;
      const clo = D(g.a[0]);
      if (clo.t === 'v') throw convErr(ctx, kind + '/' + ar + ' with an unbound closure needs call/N');
      let fv = termVars(clo);
      // a yall lambda: its parameters and the variables only it has are its own, fresh at each call
      // (yall copies the lambda); Free/Params>>Body shares Free; otherwise the variables the clause
      // also has outside the lambda are passed in (its inputs)
      if (clo.t === 'c' && clo.f === '>>' && clo.a.length === 2) {
        const ps = D(clo.a[0]);
        if (ps.t === 'c' && ps.f === '/' && ps.a.length === 2) { const free = new Set(termVars(ps.a[0])); fv = fv.filter((v) => free.has(v)); }
        else if (ctx.clause) {
          const count = (t, m) => { const st = [t]; while (st.length) { const x = D(st.pop()); if (x.t === 'v') m.set(x, (m.get(x) || 0) + 1); else if (x.t === 'c') for (const y of x.a) st.push(y); } return m; };
          const inC = count(ctx.clause, new Map()), inL = count(clo, new Map());
          fv = fv.filter((v) => (inC.get(v) || 0) > (inL.get(v) || 0));
        }
      }
      const cloKey = kind + ar + ':' + P.variantKey(Cmp('-', [list(fv), clo]));
      let nm = specs.get(cloKey);
      const nLists = kind === 'maplist' ? ar - 1 : kind === 'foldl' ? ar - 3 : 1;
      const cloName = P.name(clo) === '>>' ? 'lambda' : P.name(clo).replace(/[^A-Za-z0-9_]/g, '_');
      if (P.name(clo) === '>>') ctx.warn(kind + '/' + ar + ' lambda: variables of the lambda other than its parameters are shared with the clause (yall would copy unbound ones)');
      if (!nm) {
        nm = kind + '_' + cloName + '__s' + (++specN);
        specs.set(cloKey, nm);
        // build spec clauses
        const cm = new Map(); const c2 = copy(Cmp('-', [list(fv), clo]), cm); const fv2 = listToArray(c2.a[0]); const clo2 = c2.a[1];
        fv2.forEach((v, i) => { v.name = 'F' + (i + 1); });
        let cls = [];
        if (kind === 'maplist') {
          const Xs = [], Ts = [];
          for (let i = 0; i < nLists; i++) { Xs.push(Var('X' + (i + 1))); Ts.push(Var('T' + (i + 1))); }
          cls.push({ head: Cmp(nm, Array(nLists).fill(NIL).concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, Xs.map((x, i) => cons(x, Ts[i])).concat(fv2)), body: Cmp(',', [addArgs(clo2, Xs), Cmp(nm, Ts.concat(fv2))]) });
        } else if (kind === 'foldl') {
          const Xs = [], Ts = []; for (let i = 0; i < nLists; i++) { Xs.push(Var('X' + (i + 1))); Ts.push(Var('T' + (i + 1))); }
          const V = Var('V'), V0 = Var('V0'), V1 = Var('V1');
          cls.push({ head: Cmp(nm, Array(nLists).fill(NIL).concat([V, V], fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, Xs.map((x, i) => cons(x, Ts[i])).concat([V0, V], fv2)), body: Cmp(',', [addArgs(clo2, Xs.concat([V0, V1])), Cmp(nm, Ts.concat([V1, V], fv2))]) });
        } else if (kind === 'include' || kind === 'exclude') {
          const X = Var('X'), T = Var('T'), R = Var('R'), R1 = Var('R1');
          const keep = eq(R, cons(X, R1)), drop = eq(R, R1);
          cls.push({ head: Cmp(nm, [NIL, NIL].concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, [cons(X, T), R].concat(fv2)), body: Cmp(',', [Cmp(';', [Cmp('->', [addArgs(clo2, [X]), kind === 'include' ? keep : drop]), kind === 'include' ? drop : keep]), Cmp(nm, [T, R1].concat(fv2))]) });
        } else {
          const X = Var('X'), T = Var('T'), I = Var('I'), I1 = Var('I1'), Ex = Var('Ex'), Ex1 = Var('Ex1');
          cls.push({ head: Cmp(nm, [NIL, NIL, NIL].concat(fv2)), body: P.TRUE });
          cls.push({ head: Cmp(nm, [cons(X, T), I, Ex].concat(fv2)), body: Cmp(',', [Cmp(';', [Cmp('->', [addArgs(clo2, [X]), Cmp(',', [eq(I, cons(X, I1)), eq(Ex, Ex1)])]), Cmp(',', [eq(I, I1), eq(Ex, cons(X, Ex1))])]), Cmp(nm, [T, I1, Ex1].concat(fv2))]) });
        }
        const sk = nm + '/' + (cls[0].head.a.length);
        userPreds.add(sk);
        out.specs.push({ name: nm, kind: kind + '/' + ar, closure: show(clo), key: sk });
        const st = step('SPEC', sk, show(g), { closure: show(clo), kind: kind + '/' + ar });
        for (const cl of cls) {
          const sctx = mkNormCtx(sk, cl);
          cl.body = normGoal(cl.body, sctx);
          renameVars(Cmp('-', [cl.head, cl.body]));
          addSrc(sk, { head: cl.head, body: cl.body, spec: st.id, origText: P.showClause(Cmp(':-', [cl.head, cl.body])) });
        }
      }
      const lists = kind === 'partition' ? [g.a[1], g.a[2], g.a[3]] : g.a.slice(1);
      return Cmp(nm, lists.concat(fv));
    }
    // a cut local to a goal (findall, \+, call, condition): (A, !, B) -> (A -> B' ; fail)
    function cutLocal(g, ctx) {
      const gs = flatConj(g);
      const i = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
      if (i < 0) return g;
      rw(ctx, 'local_cut', g);
      const before = conj(gs.slice(0, i));
      const after = cutLocal(conj(gs.slice(i + 1)), ctx);
      return Cmp(';', [Cmp('->', [before, after]), P.FAIL]);
    }
    function containsNestedCut(g) {
      g = D(g);
      if (g.t !== 'c') return false;
      if (g.f === ';' && g.a.length === 2) return hasCutAnywhere(g.a[0]) || hasCutAnywhere(g.a[1]);
      if (g.f === '->' && g.a.length === 2) return hasCutAnywhere(g.a[1]);
      if (g.f === ',' && g.a.length === 2) return containsNestedCut(g.a[0]) || containsNestedCut(g.a[1]);
      return false;
    }
    function hasCutAnywhere(g) {
      g = D(g);
      if (g.t === 'a') return g.n === '!';
      if (g.t !== 'c') return false;
      if ([',', ';', '->'].includes(g.f) && g.a.length === 2) return hasCutAnywhere(g.a[0]) || hasCutAnywhere(g.a[1]);
      return false;
    }
    function hasCutAnywhereDeep(g) {
      g = D(g);
      if (g.t === 'a') return g.n === '!';
      if (g.t !== 'c') return false;
      if ([',', ';', '->'].includes(g.f) && g.a.length === 2) return hasCutAnywhereDeep(g.a[0]) || hasCutAnywhereDeep(g.a[1]);
      if (g.f === '\\+' && g.a.length === 1) return hasCutAnywhereDeep(g.a[0]);
      if ((g.f === 'findall' || g.f === 'aggregate_all') && g.a.length === 3) return hasCutAnywhereDeep(g.a[1]);
      return false;
    }
    function convErr(ctx, msg) { const e = new Error((ctx && ctx.pred ? ctx.pred + ': ' : '') + msg); e.conv = true; e.pred = ctx && ctx.pred; return e; }
    function mkNormCtx(pred, cl) {
      const ctx = { pred, rewrites: [], warn: m => out.warnings.push({ pred, msg: m }), clause: Cmp(':-', [cl.head, cl.body]) };
      // variables that occur outside bagof/setof goals (for the free-variable check)
      ctx.otherVars = new Set(termVars(cl.head));
      for (const g of flatConj(cl.body)) { const gd = D(g); if (!(gd.t === 'c' && (gd.f === 'bagof' || gd.f === 'setof'))) termVars(gd).forEach(v => ctx.otherVars.add(v)); else termVars(gd.a[2]).forEach(v => ctx.otherVars.add(v)); }
      return ctx;
    }

    for (const k of prog.order) {
      for (const cl of prog.preds.get(k)) {
        const m = new Map();
        const c = copy(Cmp(':-', [cl.head, cl.body]), m);
        // restore names from reader
        if (cl.vars) for (const [nm, v] of cl.vars) { const nv = m.get(v); if (nv) nv.name = nm; }
        const origText = P.showClause(c);
        const ctx = mkNormCtx(k, { head: c.a[0], body: c.a[1] });
        try {
          const body = normGoal(c.a[1], ctx);
          renameVars(Cmp('-', [c.a[0], body]));
          addSrc(k, { head: D(c.a[0]), body, rewrites: ctx.rewrites, origText });
        } catch (e) {
          if (!e.conv) throw e;
          out.errors.push({ pred: k, msg: e.message });
          addSrc(k, { head: D(c.a[0]), body: c.a[1], error: e.message, origText });
        }
      }
    }
    for (const k of prog.dynamic) if (!srcPreds.has(k)) { addSrc(k, null); srcPreds.set(k, []); }

    // ---- 1. analysis: calls, purity, output, recursion ----
    const info = new Map();
    for (const k of order) {
      const cls = srcPreds.get(k).filter(Boolean);
      const calls = new Set(); let impure = false; let writes = false; let cut = false; let facts = true; let maxSelf = 0; let err = false; let dyn = prog.dynamic.has(k);
      for (const cl of cls) {
        if (cl.error) err = true;
        const b = D(cl.body); if (!(b.t === 'a' && b.n === 'true')) facts = false;
        let selfCalls = 0;
        (function walk(g) {
          g = D(g); const gk = kk(g);
          if (gk === ',/2' || gk === ';/2') { walk(g.a[0]); walk(g.a[1]); return; }
          if (gk === '->/2') { impure = true; walk(g.a[0]); walk(g.a[1]); return; }
          if (gk === '\\+/1') { impure = true; walk(g.a[0]); return; }
          if (gk === 'findall/3' || gk === 'aggregate_all/3') { impure = true; walk(g.a[1]); return; }
          if (gk === '!/0') { cut = true; impure = true; return; }
          if (userPreds.has(gk) || srcPreds.has(gk)) { calls.add(gk); if (gk === k) selfCalls++; return; }
          const bk = biKind(gk, g);
          if (bk === 'effect') { writes = true; impure = true; return; }
          if (bk === 'dbeffect' || gk === 'retract/1') { impure = true; writes = true; return; }
          if (!PURE_BI.has(gk)) impure = true;
        })(cl.body);
        maxSelf = Math.max(maxSelf, selfCalls);
      }
      if (dyn) impure = true;
      info.set(k, { calls, impure, writesLocal: writes, cut, facts: facts && cls.length > 0, nclauses: cls.length, maxSelf, err, dyn });
    }
    // transitive purity / output (greatest fixpoint for purity)
    let changed = true;
    for (const [, inf] of info) { inf.pure = !inf.impure && !inf.err; inf.writes = inf.writesLocal; }
    while (changed) {
      changed = false;
      for (const [k, inf] of info) {
        for (const c of inf.calls) {
          const ci = info.get(c);
          if (!ci) continue;
          if (inf.pure && !ci.pure) { inf.pure = false; changed = true; }
          if (!inf.writes && ci.writes) { inf.writes = true; changed = true; }
        }
      }
    }
    // recursion: SCCs
    const sccOf = sccs(order, k => [...(info.get(k) || { calls: [] }).calls].filter(c => info.has(c)));
    for (const k of order) {
      const inf = info.get(k); const comp = sccOf.get(k);
      inf.recursive = comp.size > 1 || inf.calls.has(k);
      // tree recursion: some clause calls predicates of its own SCC twice or more
      let tree = false;
      for (const cl of srcPreds.get(k).filter(Boolean)) { let n = 0; (function walk(g) { g = D(g); const gk = kk(g); if (gk === ',/2' || gk === ';/2' || gk === '->/2') { walk(g.a[0]); walk(g.a[1]); return; } if (comp.has(gk)) n++; })(cl.body); if (n >= 2) tree = true; }
      inf.tree = tree;
    }
    out.info = info;

    // ---- 2. per predicate code generation ----
    const genPreds = []; // {name, arity, clauses:[term], kind, src}
    const emit = (st, term, predName) => { const cl = { term: P.copy(term), step: st.id, pred: predName }; restoreNames(term, cl.term); out.clauses.push(cl); st.clauses.push(out.clauses.length - 1); return cl; };
    function restoreNames(a, b) { /* copy keeps names already */ }

    const s2aDone = new Map();
    // S2A tables are computed once: the DET analysis needs to know which predicates become loops
    const s2aCache = new Map();
    const s2aOf = (k, f, n) => { if (!s2aCache.has(k)) s2aCache.set(k, s2aTable(prog, f, n, opts.s2aMax || 1000)); return s2aCache.get(k); };
    const detPlan = feat.det ? planDet() : new Map();
    const factRowsUsed = new Set(); // facts predicates scanned by ite_scan: their table p__rows/1 is emitted
    out.ir = new Map(); // the cut-free source the Detlog interpreter runs: normalised clauses, rule CUT applied
    for (const k of order) {
      const cls = srcPreds.get(k).filter(Boolean);
      const [f, nStr] = splitKey(k); const n = +nStr;
      const inf = info.get(k);
      {
        const err = cls.find(c => c.error);
        const topCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
        let irc = cls;
        if (!err && topCut) { const IA = []; for (let i = 0; i < n; i++) IA.push(Var('A__' + (i + 1))); irc = [cutElim(f, n, cls, IA)]; }
        out.ir.set(k, { clauses: err ? [] : irc.map(c => ({ head: c.head, body: c.body })), error: err ? err.error : null, dynamic: !!(inf && inf.dyn) });
      }
      const A = []; for (let i = 0; i < n; i++) A.push(Var('A__' + (i + 1)));
      const Rows = Var('R__0');
      const headCp = Cmp(cpName(f), A.concat([Rows]));
      const predOut = { key: k, name: f, arity: n, cpName: cpName(f) + '/' + (n + 1), kind: null, notes: [] };
      genPreds.push(predOut);
      if (cls.some(c => c.error)) {
        predOut.kind = 'error';
        const st = step('UNSUPPORTED', k, cls.map(c => c.origText).join('\n'), { reason: cls.find(c => c.error).error });
        emit(st, Cmp(':-', [headCp, Cmp('detlog_unsupported', [Cmp('/', [Atom(f), Int(n)]), Str(cls.find(c => c.error).error)])]), k);
        predOut.notes.push('not converted: ' + cls.find(c => c.error).error);
        continue;
      }
      if (!cls.length) { // dynamic, no clauses
        predOut.kind = 'empty';
        const st = step('FACTS', k, '(no clauses)', {});
        emit(st, Cmp(':-', [headCp, eq(Rows, NIL)]), k);
        if (inf.dyn) out.warnings.push({ pred: k, msg: 'dynamic predicate: clauses asserted at run time are not seen by the converted code' });
        continue;
      }
      // --- MNN S2A unfold ---
      if (feat.s2a && inf.pure && n > 0 && !queryPreds.has(k)) {
        const tab = s2aOf(k, f, n);
        if (tab.ok) {
          const spec = s2aSpec(tab.rows, n);
          predOut.kind = 's2a';
          const st = step('S2A', k, cls.map(c => c.origText).join('\n'), { rows: tab.rows.length, spec: show(spec), formula: s2aFormula(spec) });
          emit(st, Cmp(':-', [headCp, Cmp('s2a_rows', [spec, list(A), Rows])]), k);
          predOut.notes.push('unfolded: ' + tab.rows.length + ' rows; S2A loop ' + s2aFormula(spec));
          out.report.push('unfolded ' + k + ': ' + tab.rows.length + ' rows; S2A loop for I = 0..' + (tab.rows.length - 1) + ': ' + s2aFormula(spec));
          continue;
        } else if (inf.pure) predOut.notes.push('kept (not unfolded): ' + tab.why);
      } else if (feat.s2a && n > 0 && !queryPreds.has(k)) predOut.notes.push('kept (not unfolded): not pure');
      // --- FACTS ---
      const hasCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
      let memoWrap = feat.memo && inf.pure && inf.tree && n > 0 && !queryPreds.has(k);
      const detForms = detPlan.get(k);
      // MEMO and DET together: p__cp tables, p__cpc is the DET wrapper, p__cpx the packet code
      const target = detForms ? Cmp(f + '__cpx', A.concat([Rows])) : memoWrap ? Cmp(f + '__cpc', A.concat([Rows])) : headCp;
      if (detForms) { genDet(k, f, n, detForms, cls, memoWrap ? f + '__cpc' : cpName(f)); predOut.kind = 'det-mode'; predOut.notes.push('deterministic mode (DET): runs without packets when its index argument selects one clause'); }
      if (memoWrap) {
        predOut.kind = 'memo';
        const Fd = Var('F__1'), R0 = Var('R__9');
        const st = step('MEMO', k, cls.map(c => c.origText).join('\n'), { reason: 'pure and tree-recursive: variant calls give the same packet' });
        emit(st, Cmp(':-', [headCp, conj([Cmp('memo_lookup', [Cmp('/', [Atom(f), Int(n)]), list(A), Fd]), Cmp(f + '__memo', [Fd].concat(A, [Rows]))])]), k);
        emit(st, Cmp(':-', [Cmp(f + '__memo', [Cmp('found', [R0])].concat(A.map(() => Var('_')), [Rows])), eq(Rows, R0)]), k);
        emit(st, Cmp(':-', [Cmp(f + '__memo', [Atom('none')].concat(A, [Rows])), conj([Cmp(f + '__cpc', A.concat([Rows])), Cmp('memo_store', [Cmp('/', [Atom(f), Int(n)]), list(A), Rows])])]), k);
        predOut.notes.push('memoised (variant tabling of a pure tree-recursive predicate)');
      }
      if (inf.facts && !hasCut) {
        if (!predOut.kind) predOut.kind = 'facts';
        const rows = cls.map(c => E(list(c.head.t === 'c' ? c.head.a : [])));
        const st = step('FACTS', k, cls.map(c => c.origText).join('\n'), { n: cls.length });
        emit(st, Cmp(':-', [target, Cmp('cp_filter', [list(rows), list(A), Rows])]), k);
        continue;
      }
      // --- CUT elimination ---
      let work = cls;
      if (hasCut) {
        const merged = cutElim(f, n, cls, A);
        const st = step('CUT', k, cls.map(c => c.origText).join('\n'), { produced: P.showClause(Cmp(':-', [merged.head, merged.body]), { varName: v => v.name }) });
        st.clauses = []; out.cutForms = out.cutForms || {}; out.cutForms[k] = P.showClause(Cmp(':-', [merged.head, merged.body]));
        work = [merged];
        if (!predOut.kind) predOut.kind = 'cut';
      }
      if (!predOut.kind) predOut.kind = cls.length > 1 ? 'choice' : 'det';
      // --- PRED + CLAUSE ---
      if (work.length === 1) {
        genClausePacket(work[0], target, A, Rows, k, f + '__c1', true);
      } else {
        const Rs = work.map((c, i) => Var('R__' + (i + 1)));
        const st = step('PRED', k, work.map(c => c.origText || '').join('\n'), { n: work.length });
        const marks = work.some(c => hasCutAnywhereDeep(c.body));
        emit(st, Cmp(':-', [target, conj(work.map((c, i) => Cmp(f + '__c' + (i + 1), A.concat([Rs[i]]))).concat([Cmp(marks ? 'rows_cut_concat' : 'rows_concat', [list(Rs), Rows])]))]), k);
        work.forEach((c, i) => { const Ri = Var('R__0'); genClausePacket(c, Cmp(f + '__c' + (i + 1), A.concat([Ri])), A, Ri, k, f + '__c' + (i + 1), false); });
      }
    }

    // ----- DET: deterministic mode -----
    // A predicate qualifies when it writes nothing, is not dynamic, is not tabled (MEMO) or unfolded (S2A),
    // its clauses (after rule CUT) are one clause or are told apart by distinct non-variable first arguments,
    // and every body goal is true/fail, a deterministic builtin, a call of a qualifying predicate, or
    // ( C -> T ; F ) / \+ C with C a conjunction of deterministic builtins.  Greatest fixpoint over calls.
    function planDet() {
      const cand = new Map();
      for (const k of order) {
        const inf = info.get(k); const cls = srcPreds.get(k).filter(Boolean);
        if (!inf || queryPreds.has(k) || inf.err || inf.dyn || inf.writes || !cls.length || cls.some(c => c.error)) continue;
        const [f, nS] = splitKey(k); const n = +nS;
        const memo = feat.memo && inf.pure && inf.tree && n > 0;
        if (!memo && feat.s2a && inf.pure && n > 0 && s2aOf(k, f, n).ok) continue;
        const topCut = cls.some(c => flatConj(c.body).some(g => D(g).t === 'a' && D(g).n === '!'));
        let forms = cls;
        if (topCut) { const IA = []; for (let i = 0; i < n; i++) IA.push(Var('A__' + (i + 1))); forms = [cutElim(f, n, cls, IA)]; }
        // the index argument: the first position where every clause has a distinct non-variable key
        let ix = 0;
        if (forms.length > 1) {
          if (!n) continue;
          ix = -1;
          for (let j = 0; j < n && ix < 0; j++) {
            const keys = forms.map(c => firstKey(D(c.head).a[j]));
            if (!keys.some(x => x === null) && new Set(keys).size === keys.length) ix = j;
          }
          // guarded: one clause with a variable there, whose body starts with integer comparisons on that
          // variable that fail for every other clause's (integer) key, as fib(N, F) :- N > 1, ... does
          let guarded = -1;
          for (let j = 0; j < n && ix < 0; j++) {
            const keys = forms.map(c => firstKey(D(c.head).a[j]));
            const vi = keys.map((x, i) => x === null ? i : -1).filter(i => i >= 0);
            const ks = keys.filter(x => x !== null);
            if (vi.length !== 1 || new Set(ks).size !== ks.length || !ks.every(x => /^n-?\d+$/.test(x))) continue;
            const vc = forms[vi[0]], hv = D(D(vc.head).a[j]);
            const guards = [];
            for (const g of flatConj(vc.body)) { const gd = D(g); if (GUARDS()[kk(gd)] && termVars(gd).every(v => v === hv) && termVars(gd).length) guards.push(gd); else break; }
            const fails = v => guards.some(gd => { const a = evalGuard(gd.a[0], hv, v), b = evalGuard(gd.a[1], hv, v); return a !== null && b !== null && !GUARDS()[kk(gd)](a, b); });
            if (guards.length && ks.every(x => fails(+x.slice(1)))) { ix = j; guarded = vi[0]; }
          }
          if (ix < 0) continue;
          forms = forms.slice(); forms.guarded = guarded;
        } else forms = forms.slice();
        forms.ix = ix; forms.memo = memo;
        cand.set(k, forms);
      }
      let changed = true;
      while (changed) {
        changed = false;
        for (const [k, forms] of cand) if (!forms.every(c => detGoalOK(c.body, cand))) { cand.delete(k); changed = true; }
      }
      return cand;
    }
    function GUARDS() { return GUARDS.m || (GUARDS.m = { '>/2': (a, b) => a > b, '</2': (a, b) => a < b, '>=/2': (a, b) => a >= b, '=</2': (a, b) => a <= b, '=:=/2': (a, b) => a === b, '=\\=/2': (a, b) => a !== b }); }
    function evalGuard(t, hv, v) { t = D(t); if (t === hv) return v; if (t.t === 'n' && !t.f) return t.v; if (t.t === 'c' && t.a.length === 2 && '+-*'.includes(t.f) && t.f.length === 1) { const a = evalGuard(t.a[0], hv, v), b = evalGuard(t.a[1], hv, v); if (a === null || b === null) return null; return t.f === '+' ? a + b : t.f === '-' ? a - b : a * b; } return null; }
    function firstKey(t) { t = D(t); if (t.t === 'v') return null; if (t.t === 'c') return 'c' + t.f + '/' + t.a.length; if (t.t === 'a') return 'a' + t.n; if (t.t === 'n') return 'n' + t.v + (t.f ? 'f' : ''); if (t.t === 's') return 's' + t.v; return null; }
    function detGoalOK(g, cand) {
      g = D(g); const k = kk(g);
      if (k === 'true/0' || k === 'fail/0' || k === 'false/0') return true;
      if (k === ',/2') return detGoalOK(g.a[0], cand) && detGoalOK(g.a[1], cand);
      if (k === ';/2') { const l = D(g.a[0]); return isIte(l) && detGoalOK(l.a[0], cand) && detGoalOK(l.a[1], cand) && detGoalOK(g.a[1], cand); }
      if (k === '\\+/1') return detGoalOK(g.a[0], cand);
      if (userPreds.has(k) || srcPreds.has(k)) return cand.has(k);
      return isDetBi(g);
    }
    // p__cp(A.., Rows) :- copy_term(A, B), p__d(B.., S), p__dr(S, B.., A.., Rows).
    // p__dr(yes, B.., _, [e(B)]).  p__dr(no, _, _, []).  p__dr(maybe, _, A.., Rows) :- p__cpx(A.., Rows).
    // p__d(X.., S): Prolog's own clause selection and body, with status yes (one answer), no (none) or
    // maybe (a first argument was unbound where several clauses could match: the packet code decides).
    function genDet(k, f, n, forms, cls, wrapName) {
      const ix = forms.ix || 0;
      const st = step('DET', k, cls.map(c => c.origText).join('\n'), { clauses: forms.length, index: ix + 1, guarded: forms.guarded >= 0, memo: !!forms.memo });
      const mk = (p) => { const a = []; for (let i = 0; i < n; i++) a.push(Var(p + '__' + (i + 1))); return a; };
      const A = mk('A'), B = mk('B'), X = mk('X'), U = () => mk('_').map(() => Var('_'));
      const S = Var('S__0'), Rows = Var('R__0');
      const dn = f + '__d', dr = f + '__dr';
      emit(st, Cmp(':-', [Cmp(wrapName, A.concat([Rows])), conj([Cmp('copy_term', [list(A), list(B)]), Cmp(dn, B.concat([S])), Cmp(dr, [S].concat(B, A, [Rows]))])]), k);
      if (forms.memo) {
        // q__dm(X.., S): a tabled call, as a status: its packet (from the table) has no row, one row or more
        //   q__dm(X.., S) :- q__cp(X.., P), q__dms(P, X.., S).
        //   q__dms([], _.., no).   q__dms([R|Rs], X.., S) :- q__dms1(Rs, R, X.., S).
        //   q__dms1([], e(Vs), X.., S) :- if_commit([X..] = Vs, S = yes, S = no).   q__dms1([_|_], _, _.., maybe).
        const Pm = Var('P__1'), Rr = Var('R__1'), Rs = Var('R__2'), Vs = Var('V__1');
        emit(st, Cmp(':-', [Cmp(f + '__dm', X.concat([S])), conj([Cmp(cpName(f), X.concat([Pm])), Cmp(f + '__dms', [Pm].concat(X, [S]))])]), k);
        emit(st, Cmp(f + '__dms', [NIL].concat(U(), [Atom('no')])), k);
        emit(st, Cmp(':-', [Cmp(f + '__dms', [cons(Rr, Rs)].concat(X, [S])), Cmp(f + '__dms1', [Rs, Rr].concat(X, [S]))]), k);
        emit(st, Cmp(':-', [Cmp(f + '__dms1', [NIL, E(Vs)].concat(X, [S])), Cmp('if_commit', [eq(list(X), Vs), eq(S, Atom('yes')), eq(S, Atom('no'))])]), k);
        emit(st, Cmp(f + '__dms1', [cons(Var('_'), Var('_')), Var('_')].concat(U(), [Atom('maybe')])), k);
      }
      emit(st, Cmp(dr, [Atom('yes')].concat(B, U(), [list([E(list(B))])])), k);
      emit(st, Cmp(dr, [Atom('no')].concat(U(), U(), [NIL])), k);
      emit(st, Cmp(':-', [Cmp(dr, [Atom('maybe')].concat(U(), A, [Rows])), Cmp(f + '__cpx', A.concat([Rows]))]), k);
      const ctx = { n: 0 };
      const clauseCode = (c, i) => {
        const cc = copy(Cmp(':-', [c.head, c.body]));
        for (const v of termVars(cc)) v.name = (v.name && v.name !== '_' ? v.name.replace(/__+/g, '_') : 'V') + '__d' + (i + 1);
        const h = D(cc.a[0]); const hargs = h.t === 'c' ? h.a.slice() : [];
        const first = hargs[ix];
        // a head argument that is a variable seen for the first time is the argument itself: no unification
        const seen = new Set(termVars(forms.length > 1 && n ? first : NIL));
        const rest = [];
        hargs.forEach((x, j) => {
          if (j === ix && forms.length > 1) return;
          const xd = D(x);
          if (xd.t === 'v' && !seen.has(xd)) { seen.add(xd); seen.add(X[j]); xd.ref = X[j]; return; }
          termVars(xd).forEach(v => seen.add(v));
          rest.push(eq(X[j], x));
        });
        const body = detSeq(flatConj(P.resolve(cc.a[1])).map(g => P.resolve(g)), S, ctx);
        const restR = rest.map(r => P.resolve(r));
        return { first: first && P.resolve(first), code: restR.length ? Cmp('if_commit', [conj(restR), body, eq(S, Atom('no'))]) : body };
      };
      const codes = forms.map(clauseCode);
      let body;
      if (forms.length === 1) body = codes[0].code;
      else {
        let chain = eq(S, Atom('no'));
        const g = forms.guarded >= 0 ? forms.guarded : -1;
        // the guarded clause matches any value its guard admits, which excludes every key: it comes last
        if (g >= 0) chain = Cmp('if_commit', [eq(X[ix], codes[g].first), codes[g].code, chain]);
        for (let i = codes.length - 1; i >= 0; i--) if (i !== g) chain = Cmp('if_commit', [eq(X[ix], codes[i].first), codes[i].code, chain]);
        body = Cmp('if_commit', [Cmp('var', [X[ix]]), eq(S, Atom('maybe')), chain]);
      }
      emit(st, Cmp(':-', [Cmp(dn, X.concat([S])), body]), k);
    }
    function detSeq(gs, S, ctx) {
      if (!gs.length) return eq(S, Atom('yes'));
      const g = D(gs[0]), rest = gs.slice(1), k = kk(g);
      if (k === 'true/0') return detSeq(rest, S, ctx);
      if (k === 'fail/0' || k === 'false/0') return eq(S, Atom('no'));
      if (k === ',/2') return detSeq(flatConj(g).concat(rest), S, ctx);
      // a condition of deterministic builtins is an if_commit/3 condition as it stands; any other deterministic
      // condition runs with its own status Sc inside the condition: no fails it (undoing its bindings),
      // yes commits, maybe abandons the deterministic attempt
      const condOf = (C, yesCode, noCode, S1) => {
        if (flatConj(C).every(isDetBi)) return Cmp('if_commit', [C, yesCode, noCode]);
        const Sc = Var('S__' + (++ctx.n));
        return Cmp('if_commit', [conj([detSeq(flatConj(C), Sc, ctx), Cmp('\\==', [Sc, Atom('no')])]), Cmp('if_commit', [eq(Sc, Atom('yes')), yesCode, eq(S1, Atom('maybe'))]), noCode]);
      };
      if (k === ';/2') {
        const C = D(g.a[0]).a[0], T = D(g.a[0]).a[1], F = g.a[1];
        if (!rest.length) return condOf(C, detSeq(flatConj(T), S, ctx), detSeq(flatConj(F), S, ctx), S);
        const S2 = Var('S__' + (++ctx.n));
        return conj([condOf(C, detSeq(flatConj(T), S2, ctx), detSeq(flatConj(F), S2, ctx), S2), Cmp('if_commit', [eq(S2, Atom('yes')), detSeq(rest, S, ctx), eq(S, S2)])]);
      }
      if (k === '\\+/1') return condOf(g.a[0], eq(S, Atom('no')), detSeq(rest, S, ctx), S);
      if (userPreds.has(k) || srcPreds.has(k)) {
        const as = g.t === 'c' ? g.a : [];
        const dname = P.name(g) + (detPlan.has(k) && detPlan.get(k).memo ? '__dm' : '__d');
        if (!rest.length) return Cmp(dname, as.concat([S]));
        const S1 = Var('S__' + (++ctx.n));
        return conj([Cmp(dname, as.concat([S1])), Cmp('if_commit', [eq(S1, Atom('yes')), detSeq(rest, S, ctx), eq(S, S1)])]);
      }
      return Cmp('if_commit', [g, detSeq(rest, S, ctx), eq(S, Atom('no'))]);
    }

    function cutElim(f, n, cls, A) {
      // single clause  p(A1..An) :- D1
      let next = P.FAIL;
      for (let i = cls.length - 1; i >= 0; i--) {
        const m = new Map();
        const c = copy(Cmp(':-', [cls[i].head, cls[i].body]), m);
        for (const v of termVars(c)) v.name = v.name + '__c' + (i + 1);
        const h = D(c.a[0]); const hargs = h.t === 'c' ? h.a : [];
        const unif = n ? eq(list(A), list(hargs)) : P.TRUE;
        const gs = flatConj(c.a[1]);
        const ci = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
        if (ci >= 0) {
          const cond = conj([unif].concat(gs.slice(0, ci)));
          const after = laterCuts(gs.slice(ci + 1));
          next = Cmp(';', [Cmp('->', [cond, after]), next]);
        } else {
          const body = conj([unif].concat(gs));
          next = (D(next).t === 'a' && D(next).n === 'fail') ? body : Cmp(';', [body, next]);
        }
      }
      return { head: Cmp(f, A), body: next, origText: null, merged: true };
    }
    function laterCuts(gs) {
      const ci = gs.findIndex(x => D(x).t === 'a' && D(x).n === '!');
      if (ci < 0) return conj(gs);
      return Cmp(';', [Cmp('->', [conj(gs.slice(0, ci)), laterCuts(gs.slice(ci + 1))]), P.FAIL]);
    }

    // ----- clause packet -----
    function genClausePacket(cl, target, A, Rows, k, pfx, single) {
      const ctx = { pfx, n: 0, aux: 0, k, marks: hasCutAnywhereDeep(cl.body) };
      const m = new Map();
      const c = copy(Cmp(':-', [cl.head, cl.body]), m);
      const head = D(c.a[0]); const body = c.a[1];
      const hargs = head.t === 'c' ? head.a : [];
      if (cl.merged) hargs.forEach((h, i) => { const hv = D(h); if (hv.t === 'v') hv.name = 'H__' + (i + 1); });
      const Vs = termVars(Cmp('-', [head, body]));
      ctx.L = list(Vs);
      const distinctVars = hargs.every((h, i) => { const hv = D(h); return hv.t === 'v' && hargs.findIndex(x => D(x) === hv) === i; });
      // MNN: when the environment is exactly the head arguments, projecting the rows on the head renames them
      // only: the rows are the packet (rule CLAUSE with identity projection)
      const identity = (feat.det || feat.splice) && !ctx.marks && distinctVars && hargs.length === Vs.length && hargs.every((h, i) => D(h) === Vs[i]);
      const st = step('CLAUSE', k, cl.origText || P.showClause(Cmp(':-', [cl.head, cl.body])), { single, vars: Vs.map(v => v.name), identity });
      // MNN call-through:  h(V1..Vn) :- q(V1..Vn)  with distinct variables has q's packet
      const bg = D(body);
      if (identity && single && (userPreds.has(kk(bg)) || srcPreds.has(kk(bg))) && bg.t === 'c' && bg.a.length === hargs.length && bg.a.every((x, i) => D(x) === Vs[i]) && !(feat.det && detPlan.has(kk(bg)) && false)) {
        st.info.callThrough = true;
        emit(st, Cmp(':-', [Cmp(P.name(target), A.concat([Rows])), Cmp(cpName(P.name(bg)), A.concat([Rows]))]), k);
        return;
      }
      const R0 = identity ? Rows : fresh(ctx, 'R');
      const code = genGoal(body, ctx.L, R0, ctx);
      // rename the call apart and unify it with the head (resolution), then project the env rows on the head
      let proj = identity ? [] : [Cmp('project_rows', [R0, ctx.L, list(hargs), Rows])];
      if (ctx.marks && single) { const R9 = fresh(ctx, 'R'); proj = [Cmp('project_rows', [R0, ctx.L, list(hargs), R9]), Cmp('strip_cut', [R9, Rows])]; }
      // when the head arguments are distinct variables the renaming always succeeds: no decision is needed
      const rename = Cmp('copy_term', [list(A), list(hargs)]);
      const clauseBody = distinctVars ? conj([rename].concat(code, proj)) : Cmp('if_commit', [rename, conj(code.concat(proj)), eq(Rows, NIL)]);
      emit(st, Cmp(':-', [Cmp(P.name(target), A.concat([Rows])), clauseBody]), k);
      for (const ax of ctx.auxList || []) emit(ax.st, ax.term, k);
    }
    function fresh(ctx, p) { return Var(p + '__' + (++ctx.n)); }
    function auxName(ctx, kind) { return ctx.pfx + '_' + kind + (++ctx.aux); }
    function addAux(ctx, st, term) { (ctx.auxList = ctx.auxList || []).push({ st, term }); }
    // add a group of aux clauses before those of the auxiliaries generated inside them (keeps predicates contiguous, outer first)
    function insertAux(ctx, st, terms) {
      ctx.auxList = ctx.auxList || [];
      const at = ctx.auxMark !== undefined ? ctx.auxMark : ctx.auxList.length;
      for (const t of terms) ctx.auxList.push({ st, term: t });
    }

    // genGoal returns list of Detlog goals computing packet O of goal g in env L
    function genGoal(g, L, O, ctx) {
      g = D(g); const k = kk(g);
      switch (k) {
        case 'true/0': step('true', ctx.k, 'true'); return [eq(O, list([E(L)]))];
        case 'fail/0': case 'false/0': step('fail', ctx.k, 'fail'); return [eq(O, NIL)];
        case ',/2': return genConj(flatConj(g), L, O, ctx);
        case ';/2': {
          const l = D(g.a[0]);
          if (l.t === 'c' && l.f === '->' && l.a.length === 2) return genIte(l.a[0], l.a[1], g.a[1], L, O, ctx, g);
          return genDisj(flatDisj(g), L, O, ctx, g);
        }
        case '\\+/1': return genIte(g.a[0], P.FAIL, P.TRUE, L, O, ctx, g, 'neg');
        case 'findall/3': return genFindall(g, L, O, ctx, null);
        case 'aggregate_all/3': return genFindall(Cmp('findall', [aggTemplate(g.a[0]), g.a[1], Var('T__a')]), L, O, ctx, g);
        case '!/0': step('cut_mark', ctx.k, '!'); ctx.usedMarks = true; return [eq(O, list([Atom('cut'), E(L)]))];
      }
      if (userPreds.has(k) || srcPreds.has(k)) {
        const as = g.t === 'c' ? g.a : [];
        const Pk = fresh(ctx, 'P');
        const packetCall = [Cmp(cpName(P.name(g)), as.concat([Pk])), Cmp('splice_extend', [Pk, list(as), E(L), O])];
        // MNN DET-call: a deterministic-mode callee binds the environment in place; status maybe undoes that and
        // runs the packet call
        if (feat.det && detPlan.has(k) && !(feat.memo && info.get(k) && info.get(k).pure && info.get(k).tree)) {
          step('call_det', ctx.k, show(g));
          const S = fresh(ctx, 'S');
          return [Cmp('if_commit', [conj([Cmp(P.name(g) + '__d', as.concat([S])), Cmp('\\==', [S, Atom('maybe')])]),
            Cmp('if_commit', [eq(S, Atom('yes')), eq(O, list([E(L)])), eq(O, NIL)]), conj(packetCall)])];
        }
        step('call', ctx.k, show(g));
        return packetCall;
      }
      const bk = biKind(k, g);
      if (bk === 'effect' || bk === 'dbeffect') {
        if (bk === 'dbeffect') out.warnings.push({ pred: ctx.k, msg: show(g) + ': database update runs while the packet is built, in Prolog order; code that later cuts away answers may update more than Prolog would' });
        step('effect', ctx.k, show(g));
        const T = fresh(ctx, 'T');
        if (bk === 'dbeffect') return [Cmp('if_commit', [g, eq(O, list([E(L)])), eq(O, NIL)])];
        return [Cmp('effect_text', [g, T]), eq(O, list([Cmp('out', [T]), E(L)]))];
      }
      if (bk === 'nondet') {
        if (GENERATOR_BI.has(k)) step(k === 'member/2' ? 'member_cp' : 'between_cp', ctx.k, show(g)); else step('builtin_rows', ctx.k, show(g));
        if (k === 'retract/1') out.warnings.push({ pred: ctx.k, msg: 'retract/1 removes every matching clause while the packet is built' });
        const Pk = fresh(ctx, 'P');
        return [Cmp('builtin_rows', [g, Pk]), Cmp('splice_extend', [Pk, list([g]), E(L), O])];
      }
      if (bk === 'det') { step('det', ctx.k, show(g)); return [Cmp('if_commit', [g, eq(O, list([E(L)])), eq(O, NIL)])]; }
      throw convErr({ pred: ctx.k }, 'unknown procedure ' + k);
    }
    function aggTemplate(spec) { spec = D(spec); if (spec.t === 'a' && spec.n === 'count') return P.TRUE; if (spec.t === 'c' && spec.a.length === 1) return spec.a[0]; return P.TRUE; }
    function isDetBi(g) { g = D(g); const k = kk(g); if (k === 'true/0') return true; return biKind(k, g) === 'det'; }
    function isEffect(g) { g = D(g); return biKind(kk(g), g) === 'effect'; }
    function isGenerator(g) { g = D(g); const k = kk(g); if (GENERATOR_BI.has(k)) return true; return (userPreds.has(k) || srcPreds.has(k)) && info.has(k) && !info.get(k).writes; }

    function genConj(gs, L, O, ctx) {
      gs = gs.filter(g => !(D(g).t === 'a' && D(g).n === 'true'));
      if (!gs.length) return genGoal(P.TRUE, L, O, ctx);
      if (gs.length === 1) return genGoal(gs[0], L, O, ctx);
      // MNN: fuse a prefix of deterministic builtins (rule det_prefix)
      if (feat.fuse && isDetBi(gs[0])) {
        let i = 0; while (i < gs.length && isDetBi(gs[i])) i++;
        const pre = gs.slice(0, i), rest = gs.slice(i);
        step('det_prefix', ctx.k, show(conj(pre)), { n: pre.length });
        if (!rest.length) return [Cmp('if_commit', [conj(pre), eq(O, list([E(L)])), eq(O, NIL)])];
        return [Cmp('if_commit', [conj(pre), conj(genConj(rest, L, O, ctx)), eq(O, NIL)])];
      }
      // MNN: an effect followed by the rest (rule effect_prefix)
      if (feat.fuse && isEffect(gs[0])) {
        const T = fresh(ctx, 'T'), O1 = fresh(ctx, 'R');
        step('effect_prefix', ctx.k, show(gs[0]));
        return [Cmp('effect_text', [gs[0], T])].concat(genConj(gs.slice(1), L, O1, ctx), [eq(O, cons(Cmp('out', [T]), O1))]);
      }
      // MNN: splice independent generators (rule splice)
      if (feat.splice && gs.length >= 2 && isGenerator(gs[0]) && isGenerator(gs[1])) {
        const v0 = new Set(termVars(gs[0])); const shared = termVars(gs[1]).some(v => v0.has(v));
        if (!shared) {
          const st = step('splice', ctx.k, show(conj([gs[0], gs[1]])), { gens: [show(gs[0]), show(gs[1])] });
          const PA = fresh(ctx, 'P'), PB = fresh(ctx, 'P'), O1 = fresh(ctx, 'R');
          const pat = g => { g = D(g); return list(g.t === 'c' ? g.a : []); };
          const packet = (g, Pv) => { g = D(g); const k = kk(g); if (GENERATOR_BI.has(k)) return Cmp('builtin_rows', [g, Pv]); return Cmp(cpName(P.name(g)), (g.t === 'c' ? g.a : []).concat([Pv])); };
          const patB = g => { g = D(g); return GENERATOR_BI.has(kk(g)) ? list([g]) : pat(g); };
          const chain = [packet(gs[0], PA), Cmp('if_commit', [eq(PA, NIL), eq(O1, NIL), conj([packet(gs[1], PB), Cmp('splice2', [PA, PB, patB(gs[0]), patB(gs[1]), E(L), O1])])])];
          // sequential fallback, generated without splicing
          const save = feat.splice; feat.splice = false;
          const seq = genConj([gs[0], gs[1]], L, O1, ctx);
          feat.splice = save;
          const code = [Cmp('if_commit', [Cmp('splice_safe', [patB(gs[0]), patB(gs[1])]), conj(chain), conj(seq)])];
          if (gs.length === 2) { code.push(eq(O, O1)); return code; }
          return code.concat(genRows(O1, gs.slice(2), L, O, ctx));
        }
      }
      const R1 = fresh(ctx, 'R');
      const first = genGoal(gs[0], L, R1, ctx);
      return first.concat(genRows(R1, gs.slice(1), L, O, ctx));
    }
    // ROWS: map packet Rin through goals gs (each row is a copy of env L)
    function genRows(Rin, gs, L, O, ctx) {
      const nm = auxName(ctx, 's');
      const st = step('seq', ctx.k, show(conj(gs)), { aux: nm });
      const I = Var('I__1'), Is = Var('I__2'), O1 = Var('O__1'), O2 = Var('O__2'), Oo = Var('O__0'), T = Var('T__0'), Row = Var('W__0');
      const m = new Map(); const L2 = copy(L, m); // same names
      const Ob = Var('O__0');
      const code = genConj(gs.map(g => copy(g, m)), L2, Ob, ctx);
      // the four clauses are added together so the predicate stays contiguous
      const mine = [Cmp(nm, [NIL, NIL]),
        ctx.marks
          ? Cmp(':-', [Cmp(nm, [cons(I, Is), Oo]), conj([Cmp(nm + 'r', [I, O1]), Cmp('if_commit', [Cmp('cut_in', [I, O1]), eq(Oo, O1), conj([Cmp(nm, [Is, O2]), Cmp('rows_concat', [list([O1, O2]), Oo])])])])])
          : Cmp(':-', [Cmp(nm, [cons(I, Is), Oo]), conj([Cmp(nm + 'r', [I, O1]), Cmp(nm, [Is, O2]), Cmp('rows_concat', [list([O1, O2]), Oo])])]),
        Cmp(nm + 'r', [Cmp('out', [T]), list([Cmp('out', [T])])]),
        Cmp(':-', [Cmp(nm + 'r', [E(Row), Ob]), conj([Cmp('copy_term', [Row, L2])].concat(code))])];
      if (ctx.marks) mine.push(Cmp(nm + 'r', [Atom('cut'), list([Atom('cut')])]));
      insertAux(ctx, st, mine);
      return [Cmp(nm, [Rin, O])];
    }
    function genDisj(alts, L, O, ctx, g) {
      const st = step('disj', ctx.k, show(g), { n: alts.length });
      const code = []; const Rs = [];
      alts.forEach((a, i) => {
        const nm = auxName(ctx, 'd');
        const Ei = fresh(ctx, 'E'), Ri = fresh(ctx, 'R');
        code.push(Cmp('copy_term', [E(L), Ei]), Cmp(nm, [Ei, Ri])); Rs.push(Ri);
        const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0');
        const body = genGoal(copy(a, m), L2, Ob, ctx);
        addAux(ctx, st, Cmp(':-', [Cmp(nm, [E(L2), Ob]), conj(body)]));
      });
      code.push(Cmp(ctx.marks ? 'rows_concat_cut' : 'rows_concat', [list(Rs), O]));
      return code;
    }
    function genIte(C, T, F, L, O, ctx, g, kind) {
      if (feat.fuse && flatConj(C).every(isDetBi)) {
        step(kind === 'neg' ? 'neg_det' : 'ite_det', ctx.k, show(g));
        return [Cmp('if_commit', [C, conj(genGoal(T, L, O, ctx)), conj(genGoal(F, L, O, ctx))])];
      }
      const sc = feat.scan && scanShape(C);
      if (sc) return genScan(sc, T, F, L, O, ctx, g, kind);
      const st = step(kind === 'neg' ? 'neg' : 'ite', ctx.k, show(g));
      const nmC = auxName(ctx, 'k'), nm = auxName(ctx, 'i');
      const EC = fresh(ctx, 'E'), RC = fresh(ctx, 'R'), Pre = fresh(ctx, 'R'), First = fresh(ctx, 'P'), RB = fresh(ctx, 'R');
      const mine = [];
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nmC, [E(L2), Ob]), conj(genGoal(copy(C, m), L2, Ob, ctx))])); }
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nm, [NIL, E(L2), Ob]), conj(genGoal(copy(F, m), L2, Ob, ctx))])); }
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); mine.push(Cmp(':-', [Cmp(nm, [cons(E(L2), Var('_')), Var('_'), Ob]), conj(genGoal(copy(T, m), L2, Ob, ctx))])); }
      insertAux(ctx, st, mine);
      return [Cmp('copy_term', [E(L), EC]), Cmp(nmC, [EC, RC]), Cmp('packet_first', [RC, Pre, First]), Cmp(nm, [First, E(L), RB]), Cmp('rows_concat', [list([Pre, RB]), O])];
    }
    // (Pre, member(X, Xs), Post) with Pre and Post deterministic builtins: the condition's first answer is
    // the first element of Xs that passes Post.  Nothing after that element is tried, as in Prolog.
    function scanShape(C) {
      const gs = flatConj(C).filter(x => !(D(x).t === 'a' && D(x).n === 'true'));
      const i = gs.findIndex(x => !isDetBi(x));
      if (i < 0) return null;
      const gen = D(gs[i]); const gk = kk(gen);
      const post = gs.slice(i + 1);
      if (!post.every(isDetBi)) return null;
      if (gk === 'member/2' && !userPreds.has('member/2') && !srcPreds.has('member/2')) return { pre: gs.slice(0, i), gen, post };
      // a predicate of facts (no cut, not dynamic): its first answer is the first fact that unifies
      const inf = info.get(gk);
      if (inf && inf.facts && !inf.dyn && !inf.cut && !queryPreds.has(gk) && feat.factScan) return { pre: gs.slice(0, i), gen, post, facts: gk };
      return null;
    }
    // nm(Xs, e(L), O) :- if_commit(Xs = [Y|Ys], if_commit((X = Y, Post), T(L, O), nm(Ys, e(L), O)), F(L, O)).
    // The condition binds the environment in place: if_commit/3 undoes a failed attempt, and the first success
    // is the row T runs on.  An open list is extended one cell at a time, as member/2 does.
    function genScan(sc, T, F, L, O, ctx, g, kind) {
      const st = step(kind === 'neg' ? 'neg_scan' : 'ite_scan', ctx.k, show(g), { gen: show(sc.gen), filters: sc.pre.concat(sc.post).map(x => show(x)), facts: sc.facts || null });
      const nm = auxName(ctx, 'q');
      const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0');
      const Xs = Var('Y__1'), Y = Var('Y__2'), Ys = Var('Y__3');
      const gen2 = copy(sc.gen, m);
      // member/2: X = Y.  facts: the fact (renamed apart) unifies with the call's arguments
      const first = sc.facts ? Cmp('copy_term', [Y, list(gen2.t === 'c' ? gen2.a : [])]) : eq(gen2.a[0], Y);
      const cond = conj([first].concat(sc.post.map(x => copy(x, m))));
      const tC = conj(genGoal(copy(T, m), L2, Ob, ctx)), fC = conj(genGoal(copy(F, m), L2, Ob, ctx));
      const body = Cmp('if_commit', [eq(Xs, cons(Y, Ys)), Cmp('if_commit', [cond, tC, Cmp(nm, [Ys, E(L2), Ob])]), fC]);
      insertAux(ctx, st, [Cmp(':-', [Cmp(nm, [Xs, E(L2), Ob]), body])]);
      let call = [Cmp(nm, [sc.gen.a[1], E(L), O])];
      if (sc.facts) { const Tb = fresh(ctx, 'F'); factRowsUsed.add(sc.facts); call = [Cmp(P.name(sc.gen) + '__rows', [Tb]), Cmp(nm, [Tb, E(L), O])]; }
      if (!sc.pre.length) return call;
      return [Cmp('if_commit', [conj(sc.pre), conj(call), conj(genGoal(F, L, O, ctx))])];
    }
    function genFindall(g, L, O, ctx, agg) {
      const st = step(agg ? 'aggregate' : 'findall', ctx.k, show(agg || g), {});
      const Tm = g.a[0], G = g.a[1], Res = g.a[2];
      const nm = auxName(ctx, 'f');
      const EG = fresh(ctx, 'E'), TG = fresh(ctx, 'T'), RG = fresh(ctx, 'R'), Outs = fresh(ctx, 'R'), Rw = fresh(ctx, 'R'), Ts = fresh(ctx, 'T');
      { const m = new Map(); const L2 = copy(L, m); const Ob = Var('O__0'); addAux(ctx, st, Cmp(':-', [Cmp(nm, [E(L2), Ob]), conj(genGoal(copy(G, m), L2, Ob, ctx))])); }
      const code = [Cmp('copy_term', [Cmp('f', [E(L), Tm]), Cmp('f', [EG, TG])]), Cmp(nm, [EG, RG]), Cmp('packet_split', [RG, Outs, Rw]), Cmp('project_list', [Rw, EG, TG, Ts])];
      let result = Ts;
      if (agg) { const R2 = fresh(ctx, 'T'); code.push(Cmp('aggregate_list', [D(agg.a[0]).t === 'c' ? Atom(D(agg.a[0]).f) : D(agg.a[0]), Ts, R2])); result = R2; Res2(agg.a[2]); }
      function Res2() { }
      const target = agg ? agg.a[2] : Res;
      if (agg) {
        // aggregate_list fails for max/min of an empty list: then the goal has no answer
        const last = code.pop();
        code.push(Cmp('if_commit', [conj([last, eq(target, result)]), Cmp('rows_concat', [list([Outs, list([E(L)])]), O]), eq(O, Outs)]));
      } else {
        code.push(Cmp('if_commit', [eq(target, result), Cmp('rows_concat', [list([Outs, list([E(L)])]), O]), eq(O, Outs)]));
      }
      return code;
    }

    // fact tables for scans:  p__rows([[Args1], [Args2], ...]).
    for (const k of factRowsUsed) {
      const [f] = splitKey(k);
      const rows = srcPreds.get(k).filter(Boolean).map(c => list(D(c.head).t === 'c' ? D(c.head).a : []));
      const st = step('FACTS', k, srcPreds.get(k).filter(Boolean).map(c => c.origText).join('\n'), { n: rows.length, table: true });
      const at = out.clauses.findIndex(c => c.pred === k);
      const cl = { term: P.copy(Cmp(f + '__rows', [list(rows)])), step: st.id, pred: k };
      // keep the table with its predicate's other clauses
      let j = at; while (j >= 0 && j < out.clauses.length && out.clauses[j].pred === k) j++;
      if (at < 0) out.clauses.push(cl); else out.clauses.splice(j, 0, cl);
    }
    // inserting shifts clause positions: every step's clause list is rebuilt from the clauses
    if (factRowsUsed.size) { for (const st of out.steps) st.clauses = []; out.clauses.forEach((c, i) => out.steps[c.step - 1].clauses.push(i)); }

    // ---- 3. assemble ----
    out.genPreds = genPreds;
    out.srcPreds = srcPreds; out.order = order; out.prog = prog;
    // group clauses by generated predicate in order
    out.text = printDetlog(out);
    // the same program as answer streams, without packets (src/stream.js)
    if (P.toStreams) { try { out.stream = P.toStreams(out); out.streamText = out.stream.text; } catch (e) { out.streamError = e.message; } }
    // the default form is the stream code; opts.form === 'packets' keeps the packet code as the text.
    // packetText is always the packet code (the per-predicate packet entries p__cp that src/interp.js calls)
    out.packetText = out.text;
    out.form = out.streamText && opts.form !== 'packets' ? 'streams' : 'packets';
    if (out.form === 'streams') out.text = out.streamText;
    return out;
  }

  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  function sccs(nodes, succ) {
    let index = 0; const st = []; const idx = new Map(), low = new Map(), on = new Set(); const res = new Map();
    function sc(v) {
      idx.set(v, index); low.set(v, index); index++; st.push(v); on.add(v);
      for (const w of succ(v)) { if (!idx.has(w)) { sc(w); low.set(v, Math.min(low.get(v), low.get(w))); } else if (on.has(w)) low.set(v, Math.min(low.get(v), idx.get(w))); }
      if (low.get(v) === idx.get(v)) { const comp = new Set(); let w; do { w = st.pop(); on.delete(w); comp.add(w); } while (w !== v); for (const x of comp) res.set(x, comp); }
    }
    for (const v of nodes) if (!idx.has(v)) sc(v);
    return res;
  }

  // ----- S2A: answer table of a pure predicate's most general goal -----
  function s2aTable(prog, f, n, max) {
    const A = []; for (let i = 0; i < n; i++) A.push(Var());
    const g = Cmp(f, A);
    const eng = new P.Engine(prog, { stepLimit: 200000 });
    const rows = [];
    try {
      let tooMany = false;
      eng.solve(g, () => { if (rows.length >= max) { tooMany = true; return false; } rows.push(A.map(a => P.resolve(a))); return true; });
      if (tooMany) return { ok: false, why: 'more than ' + max + ' answers' };
    } catch (e) { return { ok: false, why: e.limit ? 'its table is not finite within the step limit' : 'its most general goal raises ' + (e.term ? P.errText(e.term) : e.message) }; }
    if (eng.out.length) return { ok: false, why: 'writes output' };
    if (!rows.length) return { ok: false, why: 'no answers' };
    if (!rows.every(r => r.every(P.isGround))) return { ok: false, why: 'answers are not ground' };
    return { ok: true, rows };
  }
  function s2aSpec(rows, n) {
    const K = rows.length; const cols = [];
    for (let j = 0; j < n; j++) {
      const vals = rows.map(r => D(r[j]));
      if (vals.every(v => P.compare(v, vals[0]) === 0)) { cols.push(Cmp('const', [vals[0]])); continue; }
      if (vals.every(v => v.t === 'n' && !v.f)) {
        const nw = newtonFit(vals.map(v => v.v));
        if (nw) { cols.push(Cmp('newton', [list(nw.map(Int))])); continue; }
      }
      cols.push(Cmp('data', [list(vals)]));
    }
    return Cmp('s2a', [Int(K), list(cols)]);
  }
  function newtonFit(ys) {
    const K = ys.length; const ds = []; let cur = ys.slice();
    for (let d = 0; d <= 3; d++) {
      ds.push(cur[0]);
      const next = []; for (let i = 0; i + 1 < cur.length; i++) next.push(cur[i + 1] - cur[i]);
      if (next.every(x => x === 0)) { return K >= d + 2 ? ds : null; }
      cur = next; if (!cur.length) return null;
    }
    return null;
  }
  // Newton form D0 + D1*C(I,1) + D2*C(I,2) + D3*C(I,3)  ->  integer polynomial (c0 + c1*I + c2*I^2 + c3*I^3) / den
  function newtonPoly(ds) {
    const c = [0, 0, 0, 0];
    const d = i => ds[i] || 0;
    c[0] += 6 * d(0); c[1] += 6 * d(1);
    c[1] += -3 * d(2); c[2] += 3 * d(2);
    c[1] += 2 * d(3); c[2] += -3 * d(3); c[3] += d(3);
    const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };
    let g = 6; for (const x of c) g = gcd(g, x);
    return { c: c.map(x => x / g), den: 6 / g };
  }
  function polyText(ds, I) {
    const { c, den } = newtonPoly(ds); const mon = ['', I, I + '*' + I, I + '*' + I + '*' + I];
    const parts = [];
    for (let k = 3; k >= 0; k--) { if (!c[k]) continue; const a = Math.abs(c[k]); const t = k === 0 ? String(a) : (a === 1 ? mon[k] : a + '*' + mon[k]); parts.push((c[k] < 0 ? '-' : '+') + t); }
    let s = parts.join(' ').replace(/^\+/, '').replace(/ ([+-])/g, ' $1 ') || '0';
    s = s.replace(/^-/, '-');
    return den === 1 ? s : '(' + s + ')//' + den;
  }
  function s2aFormula(spec) {
    const cols = listToArray(D(spec).a[1]);
    return cols.map((c, j) => {
      c = D(c); const nm = 'A' + (j + 1);
      if (c.f === 'const') return nm + ' = ' + show(c.a[0]);
      if (c.f === 'data') return nm + ' = data[I]';
      return nm + ' = ' + polyText(listToArray(c.a[0]).map(x => D(x).v), 'I');
    }).join(', ');
  }
  P.newtonPoly = newtonPoly; P.polyText = polyText;
  P.s2aTable = s2aTable; P.s2aSpec = s2aSpec; P.newtonFit = newtonFit; P.s2aFormula = s2aFormula;

  // ----- printing -----
  function printDetlog(out) {
    const lines = [];
    lines.push('% Detlog generated by pl2detlog (' + (out.mode === 'mnn' ? 'MNN-optimised' : 'plain') + ').');
    lines.push('% No cut, ;, ->, \\+, findall, call/N or nondeterministic builtin: every predicate p/n');
    lines.push('% becomes p__cp/n+1, which succeeds once with its answer packet of e(Row) / out(Text) items.');
    if (out.report.length) lines.push(...out.report.map(r => '% ' + r));
    for (const gp of out.genPreds) for (const n of gp.notes) if (!n.startsWith('unfolded')) lines.push('% ' + gp.key + ': ' + n);
    lines.push('');
    let last = null;
    for (const cl of out.clauses) {
      if (cl.pred !== last) { if (last !== null) lines.push(''); lines.push('% ---- ' + cl.pred + ' ----'); last = cl.pred; }
      lines.push(P.showClause(cl.term, { varName: v => v.name || ('_G' + v.id) }));
    }
    return lines.join('\n') + '\n';
  }
  P.printDetlog = printDetlog;
  P.convert = convert;
  P.flatConj = flatConj; P.conjT = conj;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
