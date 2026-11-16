/* pl2detlog source rewrites (MNN): Prolog to Prolog, before conversion, each derived from first principles.
   rewrite(src) -> { text, steps: [{ pred, rule, proof }] }; text is src itself when nothing applies.

   1. Solve for the last generator.  In a body  ..., between(Lo, Hi, X), E1 =:= E2, ...  (or a one-clause
      predicate that is such a between/3, unfolded) where X is a variable that appears once in E1 =:= E2, as
      +X or -X in a sum, and every other variable of the test is an integer bound by an earlier goal:
        E1 =:= E2  <=>  X = S  for the one integer S that isolates X (E1 - E2 is linear in X with
        coefficient +1 or -1), and between/3 enumerates each integer of [Lo, Hi] once, in order.
      So  between(Lo, Hi, X), E1 =:= E2  has the same answers, in the same order, as
          X is S, Lo =< X, X =< Hi
      (at most one answer instead of a search over Hi - Lo + 1 values).

   2. Accumulate an appended result.  A predicate
        p([], []).
        p([H|T], R) :- p(T, RT), append(RT, E, R).     (append/3, or a predicate that is append: see below)
      with E a closed list whose variables are H's, computes p(L) = p(T) ++ E.  Let acc(L, A) = p(L) ++ A.
      Then  acc([], A) = A  and  acc([H|T], A) = (p(T) ++ E) ++ A = p(T) ++ (E ++ A) = acc(T, E ++ A),
      by the associativity of ++ on proper lists, and p(L) = acc(L, []).  For a proper list L that is
        p__acc([], A, A).
        p__acc([H|T], A, R) :- p__acc(T, [e1, ..., ek|A], R).
      which is linear where p is quadratic.  Both are deterministic on a proper list, and the result is
      unified with R once it is complete in both, so a bound R gives the same answer.  For any other L
      (a partial list, a variable) p keeps its own clauses:  p(L, R) :- ( is_list(L) -> p__acc(L, [], R)
      ; p__orig(L, R) ).
      A predicate is append when its clauses are, up to renaming,
        a([], L, L).   a([H|T], L, [H|R]) :- a(T, L, R).

   3. Fuse a map into the fold that reads it.  In a body  ..., maplist(F, L, D), foldl(G, D, A0, S), ...
      (either goal may be a one-clause predicate that is just that call, unfolded) where
        F(X, Y) :- Y is E1.     (E1's only variable is X)
        G(Y, B0, B) :- B is E2.  (E2's variables are among Y, B0)   and A0 is a number,
      both goals walk the same list D element by element, so by induction on the length of L
        maplist(F, L, D), foldl(G, D, A0, S)  <=>  mf(L, D, A0, S)  where
        mf([], [], A, A).
        mf([X|Xs], [Y|Ys], B0, B) :- Y is E1, B1 is E2, mf(Xs, Ys, B1, B).
      Same answers in the same order (for an unbound L both enumerate lists by length), and the same
      errors: an error can only come from Y is E1 (X not a number), since Y and B0 are then numbers and
      B is E2 cannot fail or raise; that error is met on the same element in both. D is still built. */
(function (P) {
  'use strict';
  const D = P.deref;
  const { Cmp, Int, Atom, Var, show } = P;
  const isV = t => D(t).t === 'v';
  const keyOf = g => { g = D(g); return g.t === 'c' ? g.f + '/' + g.a.length : g.t === 'a' ? g.n + '/0' : null; };
  const conj = gs => gs.reduce((a, g) => (a ? Cmp(',', [a, g]) : g), null) || Atom('true');
  const flat = b => { b = D(b); return b.t === 'c' && b.f === ',' && b.a.length === 2 ? flat(b.a[0]).concat(flat(b.a[1])) : [b]; };
  const isNil = t => { t = D(t); return t.t === 'a' && t.n === '[]'; };
  const consOf = t => { t = D(t); return t.t === 'c' && t.f === '.' && t.a.length === 2 ? [D(t.a[0]), D(t.a[1])] : null; };
  const isTrue = b => { b = D(b); return b.t === 'a' && b.n === 'true'; };
  const intC = t => { t = D(t); return t.t === 'n' && !t.f && Number.isSafeInteger(t.v); };
  const occurs = (v, t) => { t = D(t); return t === v || (t.t === 'c' && t.a.some(a => occurs(v, a))); };
  const vars = t => P.termVars(t).map(D);

  // ---- 1. solve for the last generator ----
  // between(Lo, Hi, X) itself, or a call of a one-clause predicate g(V) :- between(Lo, Hi, V)
  function generator(prog, g) {
    g = D(g);
    if (keyOf(g) === 'between/3' && intC(g.a[0]) && intC(g.a[1]) && isV(g.a[2])) return { lo: D(g.a[0]).v, hi: D(g.a[1]).v, x: D(g.a[2]) };
    const k = keyOf(g); const cls = k && prog.preds.get(k);
    if (!cls || cls.length !== 1 || g.a.length !== 1 || !isV(g.a[0])) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (!isV(h.a[0]) || keyOf(b) !== 'between/3' || !intC(b.a[0]) || !intC(b.a[1]) || D(b.a[2]) !== D(h.a[0])) return null;
    return { lo: D(b.a[0]).v, hi: D(b.a[1]).v, x: D(g.a[0]), unfolded: k };
  }
  // the coefficient (+1 or -1) of X in an additive expression where X appears once, or 0 if not of that form
  function coef(t, x) {
    t = D(t);
    if (t === x) return 1;
    if (!occurs(x, t)) return 0;
    if (t.t === 'c' && t.a.length === 2 && t.f === '+') return coef(t.a[0], x) || coef(t.a[1], x);
    if (t.t === 'c' && t.a.length === 2 && t.f === '-') return coef(t.a[0], x) || -coef(t.a[1], x);
    if (t.t === 'c' && t.a.length === 1 && t.f === '-') return -coef(t.a[0], x);
    return NaN; // X under * or a function: not linear with a unit coefficient
  }
  const arith = t => { t = D(t); return t.t === 'v' || intC(t) || (t.t === 'c' && ((t.a.length === 2 && ['+', '-', '*'].includes(t.f)) || (t.a.length === 1 && t.f === '-')) && t.a.every(arith)); };
  // t with X replaced by 0, simplified where 0 was added or subtracted
  function zero(t, x) {
    t = D(t);
    if (t === x) return Int(0);
    if (t.t !== 'c') return t;
    const a = t.a.map(u => zero(u, x));
    const z = u => intC(u) && D(u).v === 0;
    if (t.f === '+' && a.length === 2) { if (z(a[0])) return a[1]; if (z(a[1])) return a[0]; }
    if (t.f === '-' && a.length === 2 && z(a[1])) return a[0];
    if (t.f === '-' && a.length === 1 && z(a[0])) return Int(0);
    return Cmp(t.f, a);
  }
  function solveBody(prog, gs, steps, k) {
    let changed = false;
    for (let i = 0; i + 1 < gs.length; i++) {
      const gen = generator(prog, gs[i]); if (!gen) continue;
      const t = D(gs[i + 1]); if (keyOf(t) !== '=:=/2') continue;
      const x = gen.x;
      if (gs.slice(0, i).some(g => occurs(x, g))) continue;
      const [e1, e2] = t.a.map(D);
      if (!arith(e1) || !arith(e2)) continue;
      const c1 = coef(e1, x), c2 = coef(e2, x);
      if (Number.isNaN(c1) || Number.isNaN(c2) || Math.abs(c1) + Math.abs(c2) !== 1) continue;
      // every other variable of the test: an integer from an earlier generator or is/2
      const before = gs.slice(0, i);
      const ints = new Set(before.flatMap(g => { const gg = generator(prog, g); if (gg) return [gg.x]; g = D(g); return keyOf(g) === 'is/2' && isV(g.a[0]) ? [D(g.a[0])] : []; }));
      if (!vars(t).filter(v => v !== x).every(v => ints.has(v))) continue;
      // E1 - E2 = s*X + R  =>  X = -s*R;  R = zero(E1) - zero(E2)
      const s = c1 || -c2;
      const R1 = zero(e1, x), R2 = zero(e2, x);
      const S = s === 1 ? Cmp('-', [R2, R1]) : Cmp('-', [R1, R2]);
      const solved = (intC(R1) && D(R1).v === 0) ? (s === 1 ? R2 : Cmp('-', [Int(0), R2])) : (intC(R2) && D(R2).v === 0 && s === -1) ? R1 : S;
      const repl = [Cmp('is', [x, solved]), Cmp('=<', [Int(gen.lo), x]), Cmp('=<', [x, Int(gen.hi)])];
      steps.push({ pred: k, rule: 'solve', proof: 'solve for the last generator: ' + show(gs[i]) + ', ' + show(t) + '  =>  ' + repl.map(g => show(g)).join(', ') + '  (' + show(t) + ' is linear in ' + show(x) + ' with coefficient ' + (s > 0 ? '+1' : '-1') + ' and its other variables are integers bound before; between(' + gen.lo + ', ' + gen.hi + ', ' + show(x) + ') enumerates each integer once, in order, so the one value that satisfies the test is kept if it is in range)' });
      gs.splice(i, 2, ...repl);
      changed = true;
    }
    return changed;
  }

  // ---- 2. accumulate an appended result ----
  function isAppend(prog, k) {
    if (k === 'append/3') return true;
    const cls = prog.preds.get(k); if (!cls || cls.length !== 2 || !k.endsWith('/3')) return false;
    const [b, r] = cls;
    const hb = D(b.head); if (!isTrue(b.body) || !isNil(hb.a[0]) || !isV(hb.a[1]) || D(hb.a[1]) !== D(hb.a[2])) return false;
    const hr = D(r.head); const x = consOf(hr.a[0]), z = consOf(hr.a[2]); const L = D(hr.a[1]);
    if (!x || !z || !isV(x[0]) || !isV(x[1]) || !isV(L) || z[0] !== x[0] || !isV(z[1])) return false;
    const body = flat(r.body); if (body.length !== 1 || keyOf(body[0]) !== k) return false;
    const c = D(body[0]); return D(c.a[0]) === x[1] && D(c.a[1]) === L && D(c.a[2]) === z[1] && new Set([x[0], x[1], L, z[1]]).size === 4;
  }
  function closedList(t) { const out = []; t = D(t); while (t.t === 'c' && t.f === '.' && t.a.length === 2) { out.push(D(t.a[0])); t = D(t.a[1]); } return isNil(t) ? out : null; }
  function accumulate(prog, k, steps) {
    if (!k.endsWith('/2') || prog.dynamic.has(k)) return null;
    const cls = prog.preds.get(k); if (!cls || cls.length !== 2) return null;
    const name = k.slice(0, -2);
    const base = cls.find(c => isTrue(c.body) && isNil(D(c.head).a[0]) && isNil(D(c.head).a[1]));
    const rec = cls.find(c => c !== base); if (!base || !rec || cls.indexOf(base) !== 0) return null;
    const h = D(rec.head); const ht = consOf(h.a[0]); const R = D(h.a[1]);
    if (!ht || !isV(ht[0]) || !isV(ht[1]) || !isV(R) || ht[0] === ht[1] || R === ht[0] || R === ht[1]) return null;
    const [H, T] = ht;
    const body = flat(rec.body); if (body.length !== 2) return null;
    const [call, app] = body.map(D);
    if (keyOf(call) !== k || D(call.a[0]) !== T || !isV(call.a[1])) return null;
    const RT = D(call.a[1]);
    if (!isAppend(prog, keyOf(app)) || D(app.a[0]) !== RT || D(app.a[2]) !== R) return null;
    const E = closedList(app.a[1]);
    if (!E || E.some(e => vars(e).some(v => v !== H)) || [RT, R, T].some(v => occurs(v, app.a[1]))) return null;
    // the clauses
    const acc = name + '__acc', orig = name + '__orig';
    const L = Var('L'), Rr = Var('R'), A = Var('A'), H2 = Var('H'), T2 = Var('T'), R2 = Var('R');
    const sub = new Map([[H, H2]]);
    const copyE = t => { t = D(t); if (t.t === 'v') return sub.get(t) || t; if (t.t === 'c') return Cmp(t.f, t.a.map(copyE)); return t; };
    let accA = A; for (let i = E.length - 1; i >= 0; i--) accA = Cmp('.', [copyE(E[i]), accA]);
    const A2 = Var('A');
    const clauses = [
      Cmp(':-', [Cmp(name, [L, Rr]), Cmp(';', [Cmp('->', [Cmp('is_list', [L]), Cmp(acc, [L, Atom('[]'), Rr])]), Cmp(orig, [L, Rr])])]),
      Cmp(acc, [Atom('[]'), A2, A2]),
      Cmp(':-', [Cmp(acc, [Cmp('.', [H2, T2]), A, R2]), Cmp(acc, [T2, accA, R2])])
    ];
    // the original clauses, renamed (their recursive call too)
    const ren = t => { t = D(t); if (t.t === 'c') { const a = t.a.map(ren); return Cmp(t.f === name && t.a.length === 2 ? orig : t.f, a); } if (t.t === 'a' && t.n === name) return t; return t; };
    for (const c of cls) clauses.push(isTrue(c.body) ? ren(c.head) : Cmp(':-', [ren(c.head), ren(c.body)]));
    steps.push({ pred: k, rule: 'accumulate', proof: 'accumulate the appended result of ' + k + ': p([H|T]) = p(T) ++ ' + show(app.a[1]) + '; with acc(L, A) = p(L) ++ A, acc([], A) = A and acc([H|T], A) = acc(T, ' + show(accA) + ') by the associativity of ++, and p(L) = acc(L, []) for a proper list L; any other L runs ' + k + "'s own clauses (" + orig + ')' });
    return clauses;
  }

  // ---- 3. fuse a map into the fold that reads it ----
  // a goal that is Call itself or a one-clause predicate whose body is just Call (args renamed)
  function unfoldTo(prog, g, want, n) {
    g = D(g);
    if (keyOf(g) === want) return g.a;
    const k = keyOf(g); const cls = k && prog.preds.get(k); if (!cls || cls.length !== 1 || prog.dynamic.has(k)) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (keyOf(b) !== want || !h.a.every(isV) || new Set(h.a.map(D)).size !== h.a.length) return null;
    const m = new Map(h.a.map((v, i) => [D(v), D(g.a[i])]));
    const out = b.a.map(x => { x = D(x); if (x.t === 'v') return m.has(x) ? m.get(x) : null; return vars(x).length ? null : x; });
    return out.every(x => x) ? out : null;
  }
  // F(X, Y) :- Y is E (E's variables among ins)  ->  { params, e }
  function isFn(prog, f, n) {
    f = D(f); if (f.t !== 'a') return null;
    const cls = prog.preds.get(f.n + '/' + n); if (!cls || cls.length !== 1 || prog.dynamic.has(f.n + '/' + n)) return null;
    const h = D(cls[0].head), b = D(cls[0].body);
    if (!h.a.every(isV) || new Set(h.a.map(D)).size !== n || keyOf(b) !== 'is/2' || D(b.a[0]) !== D(h.a[n - 1])) return null;
    const e = D(b.a[1]); const ins = h.a.slice(0, n - 1).map(D);
    if (!vars(e).every(v => ins.includes(v))) return null;
    return { params: h.a.map(D), e };
  }
  function fuseBody(prog, gs, steps, k, extra) {
    let changed = false;
    for (let i = 0; i + 1 < gs.length; i++) {
      const m = unfoldTo(prog, gs[i], 'maplist/3'), f = m && unfoldTo(prog, gs[i + 1], 'foldl/4'); if (!m || !f) continue;
      const [F, L, Dl] = m, [G, D2, A0, S] = f;
      if (!isV(Dl) || D(D2) !== D(Dl) || !isV(S) || D(A0).t !== 'n' || D(L) === D(Dl) || D(S) === D(Dl) || D(S) === D(L)) continue;
      const fF = isFn(prog, F, 2), fG = isFn(prog, G, 3); if (!fF || !fG) continue;
      const name = D(F).n + '__' + D(G).n + '__mapfold';
      if (!extra.has(name)) {
        const X = Var('X'), Xs = Var('Xs'), Y = Var('Y'), Ys = Var('Ys'), B0 = Var('B0'), B1 = Var('B1'), B = Var('B'), A = Var('A');
        const sub = (t, m) => { t = D(t); if (t.t === 'v') return m.get(t) || t; if (t.t === 'c') return Cmp(t.f, t.a.map(u => sub(u, m))); return t; };
        const e1 = sub(fF.e, new Map([[fF.params[0], X]])), e2 = sub(fG.e, new Map([[fG.params[0], Y], [fG.params[1], B0]]));
        extra.set(name, [Cmp(name, [Atom('[]'), Atom('[]'), A, A]),
          Cmp(':-', [Cmp(name, [Cmp('.', [X, Xs]), Cmp('.', [Y, Ys]), B0, B]), conj([Cmp('is', [Y, e1]), Cmp('is', [B1, e2]), Cmp(name, [Xs, Ys, B1, B])])])]);
      }
      const g = Cmp(name, [D(L), D(Dl), D(A0), D(S)]);
      steps.push({ pred: k, rule: 'mapfold', proof: 'fuse the map into the fold: ' + show(gs[i]) + ', ' + show(gs[i + 1]) + '  =>  ' + show(g) + '  (maplist(' + show(F) + ') and foldl(' + show(G) + ') walk the same list; by induction on its length one walk computes both, with the same answers, order and errors, since ' + show(G) + ' is an is/2 on numbers that cannot fail or raise)' });
      gs.splice(i, 2, g); changed = true;
    }
    return changed;
  }
  // a query's goal, fused where rule 3 applies; the new predicates are added to prog
  function fuseQuery(prog, term, steps) {
    const gs = flat(term), extra = new Map();
    if (!fuseBody(prog, gs, steps, 'query', extra)) return term;
    for (const cls of extra.values()) if (!prog.preds.has(keyOf(cls[0]))) for (const c of cls) prog.add(c, null);
    return conj(gs);
  }
  P.fuseQuery = fuseQuery;

  function rewrite(src) {
    let prog;
    try { prog = P.loadProgram(src); } catch (e) { return { text: src, steps: [] }; }
    const steps = [];
    const replaced = new Map(); // key -> clause terms
    const extra = new Map(); // fused predicates (rule 3)
    for (const k of prog.order) {
      const cls = prog.preds.get(k);
      const acc = accumulate(prog, k, steps);
      if (acc) { replaced.set(k, acc); continue; }
      let changed = false;
      const out = cls.map(c => {
        if (isTrue(c.body)) return c.head;
        const gs = flat(c.body);
        const a = solveBody(prog, gs, steps, k), b = fuseBody(prog, gs, steps, k, extra);
        if (a || b) { changed = true; return Cmp(':-', [c.head, conj(gs)]); }
        return Cmp(':-', [c.head, c.body]);
      });
      if (changed) replaced.set(k, out);
    }
    if (!steps.length) return { text: src, steps };
    // the program again: directives, then each predicate's clauses (rewritten ones as terms)
    const nm = () => { const names = new Map(); return v => { if (v.name && v.name !== '_' && !names.has(v)) { let n = v.name.replace(/^_+/, '') || 'V'; if (!/^[A-Z]/.test(n)) n = 'V' + n; const used = new Set(names.values()); let m = n, i = 1; while (used.has(m)) m = n + (i++); names.set(v, m); } if (!names.has(v)) names.set(v, '_G' + names.size); return names.get(v); }; };
    const lines = prog.directives.map(d => ':- ' + show(d, { quoted: true }) + '.');
    for (const k of prog.order) {
      const cls = replaced.get(k) || prog.preds.get(k).map(c => (isTrue(c.body) ? c.head : Cmp(':-', [c.head, c.body])));
      for (const c of cls) lines.push(show(c, { quoted: true, varName: nm() }) + '.');
    }
    for (const [name, cls] of extra) if (!prog.preds.has(name + '/4')) for (const c of cls) lines.push(show(c, { quoted: true, varName: nm() }) + '.');
    return { text: lines.join('\n') + '\n', steps };
  }

  P.rewrite = rewrite;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
