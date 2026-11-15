// The functions behind the 200 inputs and outputs: pl2detlog's real Prolog reader, engine,
// Prolog to Detlog converter (plain and MNN), back-converter, proofs and S2A formula finder.
import { createRequire } from 'node:module';

const require = createRequire(import.meta.url);
for (const f of ['core', 'engine', 'builtins', 'convert', 'detlog_engine', 'detlog_fast', 'detlog_interp', 'backconv', 'cgen', 'proof', 'stats', 'examples']) require(`../src/${f}.js`);
const P = globalThis.PL2D;

export const title = 'pl2detlog';

// Small Prolog programs, each with a way to make a query for it.
const PROGRAMS = {
  append: { src: 'app([],L,L).\napp([H|T],L,[H|R]) :- app(T,L,R).', query: (r) => r.pick([`app(${list(r)}, ${list(r)}, Z)`, `app(X, Y, ${list(r, 1, 3)})`]) },
  length: { src: 'len([],0).\nlen([_|T],N) :- len(T,M), N is M+1.', query: (r) => `len(${list(r)}, N)` },
  reverse: { src: 'rev(L,R) :- rev(L,[],R).\nrev([],A,A).\nrev([H|T],A,R) :- rev(T,[H|A],R).', query: (r) => `rev(${list(r)}, R)` },
  member: { src: 'mem(X,[X|_]).\nmem(X,[_|T]) :- mem(X,T).', query: (r) => `mem(X, ${list(r, 1, 4)})` },
  sum: { src: 'sum([],0).\nsum([H|T],S) :- sum(T,S1), S is S1+H.', query: (r) => `sum(${list(r)}, S)` },
  factorial: { src: 'fact(0,1) :- !.\nfact(N,F) :- N1 is N-1, fact(N1,F1), F is N*F1.', query: (r) => `fact(${r.int(0, 10)}, F)` },
  max: { src: 'mx(X,Y,X) :- X >= Y, !.\nmx(_,Y,Y).', query: (r) => `mx(${r.int(-9, 9)}, ${r.int(-9, 9)}, M)` },
  last: { src: 'last([X],X) :- !.\nlast([_|T],X) :- last(T,X).', query: (r) => `last(${list(r, 1, 5)}, X)` },
  evens: { src: 'evens([],[]).\nevens([H|T],[H|R]) :- 0 is H mod 2, !, evens(T,R).\nevens([_|T],R) :- evens(T,R).', query: (r) => `evens(${list(r)}, R)` },
  greet: { src: 'greet(N) :- write(hello(N)), nl.\ngreet_all([]).\ngreet_all([H|T]) :- greet(H), greet_all(T).', query: (r) => `greet_all(${list(r, 0, 3)})` },
  double: { src: 'dbl(X,Y) :- Y is 2*X.\ndbls([],[]).\ndbls([H|T],[D|R]) :- dbl(H,D), dbls(T,R).', query: (r) => `dbls(${list(r)}, R)` },
  grade: { src: 'grade(N,a) :- N >= 80, !.\ngrade(N,b) :- N >= 60, !.\ngrade(_,c).', query: (r) => `grade(${r.int(30, 100)}, G)` }
};
const NAMES = Object.keys(PROGRAMS);
function list(r, lo = 0, hi = 5) { return '[' + Array.from({ length: r.int(lo, hi) }, () => r.int(0, 9)).join(', ') + ']'; }
const program = (r) => { const name = r.pick(NAMES); return [name, PROGRAMS[name].query(r)]; };
const src = (name) => PROGRAMS[name].src + '\n';

// Answers, output and step counts from a run (times are left out, since they change).
const canon = (text) => JSON.stringify([...P.canonClauses(text)]);
const run = (x) => x && { ok: x.ok, answers: (x.answers || []).map((a) => a.text), output: x.output || '', error: x.error ? String(x.error.message || x.error) : null };

const TERMS = ['f(X, [a|T], "s", 1.5)', 'a+b*c', '(a:-b,c;d)', "'hello world'", '[1, 2|X]', '- 1', '-(1)', 'f(-)', '\\+ p(X)', 'X = f(Y, Y)', '{a, b}', "'\\n'", '1.0e10', 'a- -1', '[a, b, c]'];

export const cases = [
  {
    name: 'run_prolog',
    make: program,
    run: (name, query) => run(P.runQuery(P.loadProgram(src(name)), query, { stepLimit: 1e6 }))
  },
  {
    name: 'convert',
    make: (r) => { const [name, query] = program(r); return [name, query, r.pick(['plain', 'mnn'])]; },
    run: (name, query, mode) => {
      const c = P.convert(src(name), { queries: [query], mode, mnn: mode === 'mnn' });
      const heads = c.text.split('\n').filter((l) => /^[a-z'$][^ ]*__c(p|\d+)\(.*:-$/.test(l));
      return { mode: c.mode, clauses: c.clauses.length, errors: c.errors.map(String), warnings: c.warnings.length, cut_free: !/(^|[^a-z_])!/.test(c.text.replace(/%.*$/gm, '')), heads };
    }
  },
  {
    name: 'convert_and_back',
    make: (r) => [r.pick(NAMES)],
    run: (name) => {
      const c = P.convert(src(name), {});
      const b = P.backConvert(c.text, {});
      return { same_clauses: canon(b.text) === canon(src(name)), back: b.text.split('\n').filter((l) => l && !l.startsWith('%')), warnings: b.warnings.length };
    }
  },
  {
    name: 'analyse',
    make: program,
    run: (name, query) => {
      const r = P.analyse(src(name), [query], { timing: false });
      const q = r.runs[0];
      return { same: q.same, prolog: run(q.prolog).answers, detlog: run(q.plain).answers, mnn: run(q.mnn).answers, back: run(q.back).answers, proof_checks: r.proof.checks.length, proof_failed: r.proof.checks.filter((c) => c.ok === false).map((c) => c.name) };
    }
  },
  {
    name: 'newton_fit',
    make: (r) => { const c = [r.int(-5, 5), r.int(-4, 4), r.int(-2, 2), r.chance(0.3) ? r.int(-1, 1) : 0]; const n = r.int(3, 7); return [Array.from({ length: n }, (_, i) => c[0] + c[1] * (i + 1) + c[2] * (i + 1) ** 2 + c[3] * (i + 1) ** 3)]; },
    run: (ys) => { const ds = P.newtonFit(ys); return ds ? { differences: ds, formula: P.polyText(ds, 'I') } : { formula: null }; }
  },
  {
    name: 's2a_formula',
    make: (r) => { const n = r.int(3, 6), a = r.int(0, 3), b = r.int(1, 4); const k = r.pick(['x', 'y']); return [Array.from({ length: n }, (_, i) => [i + 1, a + b * (i + 1), k, (i + 1) * (i + 1) + a])]; },
    run: (rows) => {
      const terms = rows.map((row) => row.map((v) => P.readTerm(String(v)).term || P.readTerm(String(v))));
      return P.s2aFormula(P.s2aSpec(terms, rows[0].length));
    }
  },
  {
    name: 'read_and_show',
    make: (r) => [r.pick(TERMS)],
    run: (text) => { const t = P.readTerm(text); return P.show(t.term || t, { quoted: true }); }
  },
  {
    name: 'purity',
    make: (r) => [r.pick(NAMES)],
    run: (name) => { const p = P.purity(src(name)); return { pure: [...p.pure].filter(([, v]) => v).map(([k]) => k), writes: [...p.writes].filter(([, v]) => v).map(([k]) => k), order: p.prog.order }; }
  },
  {
    name: 'parse_range',
    make: (r) => [r.pick([`${r.int(-3, 5)}..${r.int(5, 20)}`, `${r.int(0, 4)}..${r.int(10, 30)} by ${r.int(2, 5)}`, Array.from({ length: r.int(1, 5) }, () => r.int(-9, 99)).join(', '), `${r.int(1, 9)} ${r.int(1, 9)} x ${r.int(1, 9)}`, ''])],
    run: (s) => P.parseRange(s)
  },
  {
    name: 'fit_growth',
    make: (r) => { const k = r.pick([0, 1, 2, 3, 'exp']); const c = r.int(1, 9); return [k, Array.from({ length: 6 }, (_, i) => { const x = 2 + 3 * i; return { x, y: k === 'exp' ? c * 2 ** x : c * x ** k }; })]; },
    run: (_, pts) => { const g = P.fitGrowth(pts); return { label: g.label, k: g.k == null ? null : Math.round(g.k * 100) / 100 }; }
  }
];
