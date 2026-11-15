// minimise.js - how much DFA (Moore) minimisation and forwarding elimination could shrink the generated Detlog:
//   node bench/minimise.js
// how much Moore-style minimisation could merge: predicates equal up to variable renaming and up to renaming
// of the predicates they call (partition refinement), plus forwarding predicates p(X..) :- q(X..)
for (const f of ['core','engine','builtins','convert','detlog_engine','detlog_fast','detlog_interp','backconv','cgen','proof','stats','examples']) require(require('path').join(__dirname, '..', 'src', f + '.js'));
const P = globalThis.PL2D; const D = P.deref;
let totP = 0, totM = 0, totF = 0, totC = 0;
for (const mnn of [false, true]) for (const ex of P.EXAMPLES) {
  const c = P.convert(ex.src, { mnn, queries: ex.queries }); const prog = P.loadProgram(c.text);
  const keys = [...prog.preds.keys()];
  let cls = new Map(keys.map(k => [k, 0]));
  const sig = k => prog.preds.get(k).map(cl => { const t = P.copy(P.Cmp(':-', [cl.head, cl.body]));
    const ren = x => { x = D(x); if (x.t === 'c') { const kk = P.key(x); const a = x.a.map(ren); const f = prog.preds.has(kk) ? '#' + cls.get(kk) + '/' + x.a.length : x.f; return { t: 'c', f, a }; } if (x.t === 'a' && prog.preds.has(x.n + '/0')) return P.Atom('#' + cls.get(x.n + '/0')); return x; };
    const h = D(t.a[0]); const head = h.t === 'c' ? P.Cmp('h', h.a.map(ren)) : P.Atom('h');
    return P.variantKey(P.Cmp(':-', [head, ren(t.a[1])])); }).join('\n');
  for (let it = 0; it < 50; it++) {
    const m = new Map(), next = new Map(); let id = 0;
    for (const k of keys) { const s = cls.get(k) + '|' + sig(k); if (!m.has(s)) m.set(s, id++); next.set(k, m.get(s)); }
    const stable = new Set(next.values()).size === new Set(cls.values()).size && keys.every(k => true);
    const before = new Set(cls.values()).size; cls = next; if (new Set(cls.values()).size === before && it > 0) break;
  }
  // forwarding: one clause, body one call with the head's arguments
  const fwd = keys.filter(k => { const c = prog.preds.get(k); if (c.length !== 1) return false; const h = D(c[0].head), b = D(c[0].body); return h.t === 'c' && b.t === 'c' && prog.preds.has(P.key(b)) && b.a.length === h.a.length && b.a.every((x, i) => D(x) === D(h.a[i])) && h.a.every((x, i) => D(x).t === 'v' && h.a.findIndex(y => D(y) === D(x)) === i); }).length;
  const merged = keys.length - new Set(cls.values()).size;
  const nCl = keys.reduce((s, k) => s + prog.preds.get(k).length, 0);
  totP += keys.length; totM += merged; totF += fwd; totC += nCl;
  if (merged || fwd) console.log((mnn ? 'MNN  ' : 'plain') + ' ' + ex.id.padEnd(10), keys.length, 'predicates;', merged, 'mergeable;', fwd, 'forwarding');
}
console.log('total', totP, 'predicates,', totC, 'clauses;', totM, 'mergeable by minimisation;', totF, 'forwarding');
