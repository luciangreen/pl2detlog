// native.js - the native tier's compiler, shared by the JavaScript JIT (detlog_fast.js) and the C export (cgen.js).
// A deterministic-mode predicate p__d(X1..Xn, S), entered with ground inputs ('i', or 'n' for an integer) and
// fresh, distinct output variables ('o'), is compiled for that mode to a function of its inputs that returns its
// outputs, or NO / MAYBE: ground terms in and out, no logic variables, no trail, integer arithmetic on raw
// integers, direct calls between native functions, tabled calls memoised.  The analysis is abstract
// interpretation over the Detlog of p__d: each variable is G (ground: a local holds it; int: it is a raw
// integer), F (fresh), P (pending: built from parts that become ground later) or U (unknown: give up).
// Anything the analysis cannot follow throws NOPE: no native function for that mode.  The emitter (EM) gives
// the target language; the analysis and the decisions are the same for every target.
(function (P) {
  'use strict';
  const D = P.deref, Cmp = P.Cmp;
  const termVars = P.termVars;
  const NOPE = { nope: true };
  function nope() { if (P.NATIVE_DEBUG) P.NATIVE_WHY = new Error().stack.split('\n')[2]; throw NOPE; }
  function sameTerm(a, b) { a = D(a); b = D(b); if (a === b) return true; if (a.t !== b.t) return false; if (a.t === 'c') return a.f === b.f && a.a.length === b.a.length && a.a.every((x, i) => sameTerm(x, b.a[i])); if (a.t === 'a') return a === b; if (a.t === 'n') return a.v === b.v && a.f === b.f; if (a.t === 's') return a.v === b.v; return false; }

  // one function: returns { src, intRet, params, outs } for EM to place, or throws NOPE
  function genNative(prog, k, mode, fnName, need, selfInt, EM) {
    const cls = prog.preds.get(k); if (!cls || cls.length !== 1) nope();
    const cl = P.copy(Cmp('-', [cls[0].head, cls[0].body]));
    const head = D(cl.a[0]); const n = head.a.length - 1;
    const S0 = D(head.a[n]); if (S0.t !== 'v') nope();
    const jsName = new Map(); let nv = 0, nl = 0;
    const js = v => { let x = jsName.get(v); if (!x) { x = 'v' + (nv++); jsName.set(v, x); } return x; };
    const used = new Map(); // local name|int -> {name, int}
    const V = x => { if (!x.param) used.set(x.js + '|' + !!x.int, { name: x.js, int: !!x.int }); return EM.v(x.js, !!x.int); };
    let st = new Map(); const params = [], outs = [];
    st.set(S0, { k: 'TOP' });
    for (let i = 0; i < n; i++) {
      const hv = D(head.a[i]); if (hv.t !== 'v' || st.has(hv)) nope();
      if (mode[i] === 'i') { st.set(hv, { k: 'G', js: 'a' + i, param: true }); params.push({ name: 'a' + i, int: false }); }
      else if (mode[i] === 'n') { st.set(hv, { k: 'G', js: 'a' + i, int: true, param: true }); params.push({ name: 'a' + i, int: true }); }
      else { st.set(hv, { k: 'F' }); outs.push(hv); }
    }
    const statusLocals = new Set(); const statusOf = new Map();
    const get = (s, v) => s.get(v) || { k: 'F' };
    const clone = s => new Map(s);
    const join = (a, b) => {
      if (!a) return b; if (!b) return a;
      const r = new Map();
      for (const v of new Set([...a.keys(), ...b.keys()])) {
        const x = get(a, v), y = get(b, v);
        if (x.k === y.k && x.js === y.js && x.t === y.t && x.set === y.set && !!x.int === !!y.int) r.set(v, x); else r.set(v, { k: 'U' });
      }
      return r;
    };
    const ATOM = { yes: EM.YES, no: EM.NO, maybe: EM.MAYBE };
    const isStatusAtom = t => { t = D(t); return t.t === 'a' && ATOM[t.n] !== undefined; };
    const G_ = (s, v, int) => { s.set(v, { k: 'G', js: js(v), int: !!int }); return V(s.get(v)); };
    const allG = (t, s) => termVars(t).every(v => { const x = get(s, v); return x.k === 'G' || (x.k === 'P' && allG(x.t, s)); });
    const build = (t, s) => {
      t = D(t);
      if (t.t === 'v') { const x = get(s, t); if (x.k === 'G') return x.int ? EM.box(V(x)) : V(x); if (x.k === 'P') return build(x.t, s); nope(); }
      if (t.t !== 'c' || P.isGround(t)) return EM.k(t);
      return EM.cmp(t.f, t.a.map(x => build(x, s)));
    };
    let tmp = 0;
    // match a ground value (an expression) against a pattern: binds fresh variables, tests the rest
    function match(expr, pat, s, fail) {
      pat = D(pat);
      if (pat.t === 'v') {
        const x = get(s, pat);
        if (x.k === 'F') return EM.assign(G_(s, pat, false), expr);
        if (x.k === 'G') return 'if (!' + (x.int ? EM.isIntVal(expr, V(x)) : EM.eq(expr, V(x))) + ') ' + fail + '\n';
        if (x.k === 'P') return match(expr, x.t, s, fail);
        nope();
      }
      const t = 't' + (tmp++);
      if (pat.t !== 'c') return '{ ' + EM.tmp(t, expr) + ' if (!(' + EM.keyTest(pat, t) + ')) ' + fail + ' }\n';
      let code = '{ ' + EM.tmp(t, expr) + '\nif (!(' + EM.isCmp(t, pat.f, pat.a.length) + ')) ' + fail + '\n';
      pat.a.forEach((y, i) => { code += match(EM.arg(t, i), y, s, fail); });
      return code + '}\n';
    }
    // unification in functional mode; returns code, or null for a unification that fails statically
    function unify(a, b, s, fail) {
      a = D(a); b = D(b);
      if (a === b) return '';
      const xa = a.t === 'v' ? get(s, a) : null, xb = b.t === 'v' ? get(s, b) : null;
      if (xa && xa.k === 'U' || xb && xb.k === 'U') nope();
      if (xa && xa.k === 'F') {
        // an integer stays a raw integer: an integer constant, or another variable holding one
        if (b.t === 'n' && !b.f && Number.isSafeInteger(b.v)) return EM.assign(G_(s, a, true), EM.num(b.v));
        if (xb && xb.k === 'G' && xb.int) { const rhs = V(xb); return EM.assign(G_(s, a, true), rhs); }
        if (allG(b, s)) { const rhs = build(b, s); return EM.assign(G_(s, a, false), rhs); }
        if (termVars(b).includes(a)) nope(); s.set(a, { k: 'P', t: b }); return '';
      }
      if (xb && xb.k === 'F') return unify(b, a, s, fail);
      if (xa && xa.k === 'P') return unify(xa.t, b, s, fail);
      if (xb && xb.k === 'P') return unify(a, xb.t, s, fail);
      if (xa && xb) {
        if (xa.int && xb.int) return 'if (' + V(xa) + ' ' + EM.NEOP + ' ' + V(xb) + ') ' + fail + '\n';
        if (xa.int || xb.int) { const [i, t] = xa.int ? [xa, xb] : [xb, xa]; return 'if (!' + EM.isIntVal(V(t), V(i)) + ') ' + fail + '\n'; }
        return 'if (!' + EM.eq(V(xa), V(xb)) + ') ' + fail + '\n';
      }
      if (xa && xa.int) return intMatch(V(xa), b, fail);
      if (xb && xb.int) return intMatch(V(xb), a, fail);
      if (xa) return match(V(xa), b, s, fail);
      if (xb) return match(V(xb), a, s, fail);
      if (a.t !== b.t) return null;
      if (a.t === 'c') {
        if (a.f !== b.f || a.a.length !== b.a.length) return null;
        let code = '';
        for (let i = 0; i < a.a.length; i++) { const c = unify(a.a[i], b.a[i], s, fail); if (c === null) return null; code += c; }
        return code;
      }
      return sameTerm(a, b) ? '' : null;
    }
    // an integer against a pattern: only an equal integer constant unifies
    function intMatch(v, pat, fail) {
      pat = D(pat);
      if (pat.t === 'n' && !pat.f) return 'if (' + v + ' ' + EM.NEOP + ' ' + EM.num(pat.v) + ') ' + fail + '\n';
      return fail + '\n';
    }
    // integer arithmetic on ground values; unbox bails on anything but an integer
    const OPS = { '+': 'IADD', '-': 'ISUB', '*': 'IMUL' };
    const FNS = { '//': 'IDIV', mod: 'IMOD', rem: 'IREM', min: 'MIN', max: 'MAX' };
    function arith(t, s) {
      t = D(t);
      if (t.t === 'n') { if (t.f || !Number.isSafeInteger(t.v)) nope(); return '(' + EM.num(t.v) + ')'; }
      if (t.t === 'v') { const x = get(s, t); if (x.k !== 'G') nope(); return x.int ? V(x) : EM.unbox(V(x)); }
      if (t.t !== 'c') nope();
      if (t.a.length === 2) {
        const a = arith(t.a[0], s), b = arith(t.a[1], s);
        if (OPS[t.f]) return EM.fn(OPS[t.f], [a, b]); // checked: overflow bails out
        if (FNS[t.f]) return EM.fn(FNS[t.f], [a, b]);
        nope();
      }
      if (t.a.length === 1 && t.f === '-') return EM.fn('ISUB', ['(0)', arith(t.a[0], s)]);
      if (t.a.length === 1 && t.f === 'abs') return EM.fn('ABS', [arith(t.a[0], s)]);
      nope();
    }
    const CMPN = { '=:=': EM.EQOP, '=\\=': EM.NEOP, '<': '<', '>': '>', '=<': '<=', '>=': '>=' };
    let intRet = outs.length === 1;
    const RET = s => {
      if (outs.length === 1) {
        const x = get(s, outs[0]);
        if (!(x.k === 'G' && x.int)) intRet = false;
        if (selfInt) { if (!(x.k === 'G' && x.int)) nope(); return EM.retOuts([V(x)], true); }
      }
      return EM.retOuts(outs.map(v => build(v, s)), false);
    };
    let lab = 0;
    // compile a goal; fail is the statement run when it fails; returns { code, out } (out = state after,
    // null when control never falls through)
    function G(g, s, fail) {
      g = D(g); const kk = P.key(g);
      if (kk === ',/2') {
        const gs = P.flatConj(g); let code = '', cur = s;
        for (const x of gs) { if (!cur) break; const r = G(x, cur, fail); code += r.code; cur = r.out; }
        return { code, out: cur };
      }
      if (kk === 'true/0') return { code: '', out: s };
      if (kk === 'fail/0' || kk === 'false/0') return { code: fail + '\n', out: null };
      if (kk === 'if_commit/3') {
        const L = 'c' + (lab++), ok = 'ok' + L, LF = EM.fail(L);
        const rc = G(g.a[0], clone(s), LF);
        const rt = rc.out ? G(g.a[1], rc.out, fail) : null;
        // a condition that cannot fail is just its code then the then-branch
        if (rt && !rc.code.includes(LF)) return { code: rc.code + rt.code, out: rt.out };
        const re = G(g.a[2], clone(s), fail);
        if (!rt) return { code: rc.code === LF + '\n' ? re.code : EM.blockNoThen(L, rc.code, re.code), out: re.out };
        // a single test:  if (test) else-branch, otherwise then-branch
        const one = rc.code.startsWith('if (') && rc.code.endsWith(') ' + LF + '\n') && rc.code.indexOf('\n') === rc.code.length - 1 ? rc.code.slice(4, rc.code.length - LF.length - 3) : null;
        if (one !== null && !one.includes(LF)) return { code: 'if (' + one + ') {\n' + re.code + '} else {\n' + rt.code + '}\n', out: join(rt.out, re.out) };
        return { code: EM.block(L, ok, rc.code, rt.code, re.code), out: join(rt.out, re.out) };
      }
      if (kk === 'var/1' || kk === 'nonvar/1') {
        const x = D(g.a[0]); const xs = x.t === 'v' ? get(s, x) : { k: 'G' };
        if (xs.k === 'U' || xs.k === 'P') nope();
        const isVar = xs.k === 'F';
        return (kk === 'var/1') === isVar ? { code: '', out: s } : { code: fail + '\n', out: null };
      }
      if (kk === '=/2' || kk === '\\==/2' || kk === '==/2') {
        const a = D(g.a[0]), b = D(g.a[1]);
        const sa = a.t === 'v' && get(s, a), sb = b.t === 'v' && get(s, b);
        const stat = x => x && (x.k === 'TOP' || x.k === 'S');
        if (stat(sa) || stat(sb) || isStatusAtom(a) || isStatusAtom(b)) return statusGoal(kk, a, b, s, fail);
        if (kk === '=/2') { const s2 = clone(s); const c = unify(a, b, s2, fail); if (c === null) return { code: fail + '\n', out: null }; return { code: c, out: s2 }; }
        if (!allG(a, s) || !allG(b, s)) nope();
        return { code: 'if (' + (kk === '==/2' ? '!' : '') + EM.eq(build(a, s), build(b, s)) + ') ' + fail + '\n', out: s };
      }
      if (kk === 'is/2') {
        const x = D(g.a[0]), e = arith(g.a[1], s);
        const s2 = clone(s);
        if (x.t === 'v' && get(s, x).k === 'F') return { code: EM.assign(G_(s2, x, true), e), out: s2 };
        return { code: 'if (' + arith(x, s) + ' ' + EM.NEOP + ' ' + e + ') ' + fail + '\n', out: s };
      }
      if (CMPN[g.f] && g.t === 'c' && g.a.length === 2) return { code: 'if (!(' + arith(g.a[0], s) + ' ' + CMPN[g.f] + ' ' + arith(g.a[1], s) + ')) ' + fail + '\n', out: s };
      // a tabled call (q__dm): the native call of q__d for that mode, memoised on its ground inputs
      const memo = g.t === 'c' && /__dm$/.test(g.f) && prog.preds.has(g.f.slice(0, -1) + '/' + g.a.length);
      if (memo || (g.t === 'c' && /__d$/.test(g.f) && prog.preds.has(kk))) {
        const dk = memo ? g.f.slice(0, -1) + '/' + g.a.length : kk;
        const as = g.a.slice(0, -1), Sx = D(g.a[g.a.length - 1]);
        let m = ''; const ins = [], os = [];
        for (const a of as) {
          const ad = D(a);
          if (ad.t === 'v' && get(s, ad).k === 'F' && !os.includes(ad)) { m += 'o'; os.push(ad); }
          else if (ad.t === 'v' && get(s, ad).k === 'G' && get(s, ad).int) { m += 'n'; ins.push(V(get(s, ad))); }
          else if (ad.t === 'n' && !ad.f && Number.isSafeInteger(ad.v)) { m += 'n'; ins.push(EM.num(ad.v)); }
          else if (allG(a, s)) { m += 'i'; ins.push(build(a, s)); }
          else nope();
        }
        if (os.some(v => as.filter(a => termVars(a).includes(v)).length > 1)) nope();
        const cinfo = need(dk, m), callee = cinfo.name;
        const s2 = clone(s);
        const outT = os.map(v => G_(s2, v, os.length === 1 && cinfo.retInt));
        const sx = get(s, Sx);
        const rs = 's' + (nl++); statusLocals.add(rs);
        const call = EM.call(callee, ins, outT, os.length === 1 && cinfo.retInt, rs, memo && os.length <= 1 ? { table: dk + '|' + m, mode: m } : null);
        if (sx.k === 'TOP') return { code: '{ ' + call + 'if (' + rs + ' ' + EM.NEOP + ' ' + EM.YES + ') ' + EM.retStatus(rs) + '\n' + RET(s2) + ' }\n', out: null };
        if (sx.k !== 'F') nope();
        s2.set(Sx, { k: 'S', js: rs, set: true });
        return { code: call, out: s2 };
      }
      nope();
    }
    // status variables: the top S returns; local ones are assigned once, then tested
    function statusGoal(kk, a, b, s, fail) {
      const val = (t, x) => isStatusAtom(t) ? ATOM[D(t).n] : x && x.k === 'S' && x.set ? x.js : null;
      let sa = D(a).t === 'v' ? get(s, D(a)) : null, sb = D(b).t === 'v' ? get(s, D(b)) : null;
      if (kk === '=/2') {
        if (sb && sb.k === 'TOP') { [a, b] = [b, a]; [sa, sb] = [sb, sa]; }
        if (sa && sa.k === 'TOP') {
          const v = val(b, sb); if (!v) nope();
          if (v === EM.YES) return { code: RET(s) + '\n', out: null };
          if (v === EM.NO || v === EM.MAYBE) return { code: EM.retStatus(v) + '\n', out: null };
          // after if_commit(S1 = yes, .., S = S1) the value cannot be yes, and the outputs need not exist
          let ret; const keep = intRet; try { ret = RET(s); } catch (e) { if (e !== NOPE) throw e; ret = EM.BAIL; intRet = keep; }
          return { code: 'if (' + v + ' ' + EM.EQOP + ' ' + EM.YES + ') { ' + ret + ' }\n' + EM.retStatus(v) + '\n', out: null };
        }
        if (sb && (sb.k === 'F') && !(sa && sa.k === 'F')) { [a, b] = [b, a]; [sa, sb] = [sb, sa]; }
        if (sa && sa.k === 'F') { // a fresh local status takes a value
          const v = val(b, sb); if (!v) nope();
          // one local per status variable, so both branches of an if_commit/3 set the same one (they join)
          let sv = statusOf.get(D(a)); if (!sv) { sv = 's' + (nl++); statusOf.set(D(a), sv); } statusLocals.add(sv);
          const s2 = clone(s); s2.set(D(a), { k: 'S', js: sv, set: true });
          return { code: sv + ' = ' + v + ';\n', out: s2 };
        }
        const va = val(a, sa), vb = val(b, sb); if (!va || !vb) nope();
        return { code: 'if (' + va + ' ' + EM.NEOP + ' ' + vb + ') ' + fail + '\n', out: s };
      }
      const va = val(a, sa), vb = val(b, sb); if (!va || !vb) nope();
      return { code: 'if (' + va + ' ' + (kk === '==/2' ? EM.NEOP : EM.EQOP) + ' ' + vb + ') ' + fail + '\n', out: s };
    }
    const body = G(cl.a[1], st, EM.BAIL);
    return { src: EM.func(fnName, params, outs.length, selfInt, [...used.values()], [...statusLocals], body.code), intRet };
  }

  // a batch: the root (k, mode) and every native function it calls that is not compiled yet, with the fixpoint
  // over which single-output functions return raw integers.  done: key -> { name, retInt } of earlier batches
  // (null when refused).  Returns Map key -> { name, src, retInt }, or null when refused.
  function nativeBatch(prog, k, mode, EM, done, newName) {
    let batch = new Map();
    const retInt = new Map();
    try {
      const need = (k2, m2) => {
        const key2 = k2 + '|' + m2;
        if (done.has(key2)) { const f = done.get(key2); if (!f) nope(); return { name: f.ref, retInt: !!f.retInt }; }
        if (batch.has(key2)) return { name: batch.get(key2).name, retInt: !!retInt.get(key2) };
        const name = newName(key2);
        const ent = { name, src: null }; batch.set(key2, ent);
        const g = genNative(prog, k2, m2, name, need, !!retInt.get(key2), EM);
        ent.src = g.src; ent.intRet = g.intRet; ent.k = k2; ent.mode = m2;
        return { name, retInt: !!retInt.get(key2) };
      };
      for (let pass = 0; ; pass++) {
        batch = new Map(); EM.reset && EM.reset(); need(k, mode);
        let changed = false;
        for (const [key2, e] of batch) if (e.intRet !== !!retInt.get(key2)) { retInt.set(key2, e.intRet); changed = true; }
        if (!changed) break;
        if (pass > 6) nope();
      }
      for (const [key2, e] of batch) e.retInt = !!retInt.get(key2);
      return batch;
    } catch (e) {
      if (e !== NOPE) throw e;
      if (P.NATIVE_DEBUG) console.log('native refused', k + '|' + mode, P.NATIVE_WHY);
      return null;
    }
  }
  P.nativeGen = genNative;
  P.nativeBatch = nativeBatch;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
