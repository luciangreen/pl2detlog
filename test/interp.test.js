// interp.test.js - the interpreter (src/interp.js) with SWI-Prolog's library (src/swi.js) and the
// thermodynamic compression MNN (src/thermo.js):
//   * thermo: mnns's examples, the exhaustive proof, and the store's round trip;
//   * SWI-Prolog programs: dicts, JSON, strings, streams and files, modules, yall, halt codes,
//     dict functional notation, portray_clause, b_setval, limits;
//   * routes: every route the interpreter picks gives Prolog's answers and output, and the store
//     keeps the pick (as thermo codes where that is smaller and not slower);
//   * compiled C (when there is a C compiler): the interpreter's C route prints what Prolog prints.
'use strict';
const test = require('node:test'), assert = require('node:assert');
const path = require('path'), fs = require('fs'), os = require('os'), cp = require('child_process');
for (const f of ['core', 'engine', 'builtins', 'swi', 'convert', 'stream', 'detlog_engine', 'native', 'detlog_fast', 'detlog_interp', 'backconv', 'algebra', 'rewrite', 'cgen', 'proof', 'stats', 'cref', 'examples', 'thermo', 'interp']) require(path.join(__dirname, '..', 'src', f + '.js'));
const P = globalThis.PL2D;
P.C_RUNTIME = fs.readFileSync(path.join(__dirname, '..', 'src', 'runtime.c'), 'utf8');

function memIO(files) {
  const m = new Map(Object.entries(files));
  return { cwd: '', files: m, readFile: (p) => (m.has(p) ? m.get(p) : null), writeFile: (p, s, ap) => m.set(p, (ap && m.get(p) || '') + s), stat: (p) => (m.has(p) ? 'file' : null), list: () => [...m.keys()], deleteFile: (p) => { if (!m.has(p)) { const e = new Error('no file'); e.code = 'ENOENT'; throw e; } m.delete(p); }, rename: (a, b) => { m.set(b, m.get(a)); m.delete(a); } };
}
function swipl(files, args, opts = {}) {
  let out = '', err = '';
  const it = new P.Interpreter(Object.assign({ io: memIO(files) }, opts));
  const code = it.runArgs(args, { out: (s) => { out += s; }, err: (s) => { err += s; } });
  return { code, out, err, it };
}

test('thermo: the examples of mnns docs/thermo.md', () => {
  const T = P.thermo;
  const c = T.compress([...'banana']);
  assert.deepStrictEqual([c.alphabet, c.counts, c.rank], [['a', 'b', 'n'], [3, 1, 2], 34n]);
  assert.strictEqual(T.decompress(c).join(''), 'banana');
  assert.deepStrictEqual(T.neurons([...'banana']).map((n) => n.weight), [30n, 0n, 3n, 0n, 1n, 0n]);
  const r = T.report([...'abracadabra']);
  assert.deepStrictEqual([r.rank, r.classSize, r.rankBits, r.compositionBits, r.rawBits, r.entropyBits, r.erasedBitsIrreversible, r.landauerJoules300K], [21519n, 83160n, 17, 11, 33, 22.444, 5, 1.435e-20]);
  assert.strictEqual(T.decompress({ alphabet: ['a', 'b'], counts: [1, 1], rank: 2n }), null, 'a rank outside 0..M-1 does not decode');
});

test('thermo: the proof checks every sequence of the domain', () => {
  const p = P.thermo.prove(['a', 'b', 'c'], 6);
  assert.ok(p.proof, JSON.stringify(p));
  assert.deepStrictEqual(p.proof.map((s) => s.name), ['thermo_round_trip', 'thermo_bijection', 'thermo_neuron_sum', 'thermo_entropy_bound', 'thermo_landauer']);
  assert.strictEqual(p.proof[0].verified.count, 1093);
  assert.ok(P.thermo.prove(['x', 'y', 'z', 'w'], 5).proof);
});

test('thermo: the store gives back every text', () => {
  const texts = ['', 'a', 'banana', 'ünïcödé • text\n', fs.readFileSync(path.join(__dirname, '..', 'src', 'thermo.js'), 'utf8')];
  for (let i = 0; i < 40; i++) texts.push(Array.from({ length: i * 7 }, (_, j) => String.fromCharCode(97 + ((i * j) % (1 + i % 9)))).join(''));
  for (const t of texts) for (const block of [1, 16, 128, 1000]) assert.strictEqual(P.thermo.unpack(P.thermo.pack(t, { block })), t);
  const big = texts[4], u = P.thermo.pack(big);
  assert.ok(u.length < big.length * 0.8, 'source text is stored in under 80% of its characters');
  assert.throws(() => P.thermo.unpack(new Uint8Array([1, 2, 3])));
});

test('SWI-Prolog programs: dicts, JSON, strings, files, modules, yall, halt', () => {
  const files = {
    'json.pl': ':- use_module(library(http/json)).\nmain :- atom_json_dict(\'{"name":"Ann","n":[1,2,3]}\', D, []), sum_list(D.n, S), format("~w ~w~n", [D.name, S]), D2 = D.put(age, 30), atom_json_dict(A, D2, [width(0)]), writeln(A).\n',
    'strings.pl': 'main :- split_string("a,b,,c", ",", "", P), length(P, N), string_concat(X, "lo", "hello"), sub_atom(abcde, 1, 3, _, S), format("~w ~w ~q ~w~n", [N, X, P, S]).\n',
    'module.pl': ':- module(m, [run/1]).\nrun(X) :- helper(X, Y), format("~w~n", [Y]).\nhelper(X, Y) :- Y is X * 2.\n',
    'uses.pl': ':- use_module(module).\nhelper(_, never).\nmain :- run(21), helper(1, Z), writeln(Z).\n',
    'files.pl': 'main :- open(\'out.txt\', write, S), format(S, "line ~w~n", [1]), close(S), setup_call_cleanup(open(\'out.txt\', read, R), read_line_to_string(R, L), close(R)), writeln(L), ( catch(delete_file(nope), error(E, _), (print(E), nl)) -> true ; true ).\n',
    'halt.pl': ':- initialization(main, main).\nmain :- writeln(start), halt(3).\n',
    'fail.pl': 'main :- member(X, [1,2]), X > 5.\n',
    'err.pl': 'main :- X is foo + 1, writeln(X).\n',
    'lambda.pl': ':- use_module(library(yall)).\nmain :- maplist([X, Y]>>(Y is X * X), [1,2,3], L), foldl([X, A0, A]>>(A is A0 + X), L, 0, S), print(L-S), nl, convlist([X, Y]>>(X > 1, Y = x(X)), [1,2,3], C), print(C), nl.\n',
    'write.pl': 'main :- X = f(A, [1,2], "s", \'A b\', 1+2, (a:-b,c)), write(X), nl, print(X), nl, writeq(- 1), nl, portray_clause((p(A1) :- q(A1, _), ( r -> s ; t ))), nl.\n',
    'bval.pl': 'main :- b_setval(v, 1), ( b_setval(v, 2), fail ; true ), b_getval(v, X), writeln(X), call_with_inference_limit(loop, 1000, R), writeln(R).\nloop :- loop.\n',
    'args.pl': 'main :- current_prolog_flag(argv, A), print(A), nl.\n'
  };
  const r = (args) => swipl(files, args);
  assert.deepStrictEqual(r(['-g', 'main', '-t', 'halt', 'json.pl']).out, 'Ann 6\n{"age":30, "n":[1, 2, 3], "name":"Ann"}\n');
  assert.deepStrictEqual(r(['-g', 'main', '-t', 'halt', 'strings.pl']).out, '4 hel ["a","b","","c"] bcd\n');
  assert.deepStrictEqual(r(['-g', 'main', '-t', 'halt', 'uses.pl']).out, '42\nnever\n', 'the module\'s helper/2 is its own');
  const f = r(['-g', 'main', '-t', 'halt', 'files.pl']);
  assert.deepStrictEqual(f.out, 'line 1\nexistence_error(file,nope)\n');
  assert.deepStrictEqual([r(['halt.pl']).code, r(['halt.pl']).out], [3, 'start\n']);
  const fl = r(['-g', 'main', '-t', 'halt', 'fail.pl']); assert.deepStrictEqual([fl.code, /failed/.test(fl.err)], [1, true]);
  const er = r(['-g', 'main', '-t', 'halt', 'err.pl']); assert.deepStrictEqual([er.code, /type_error|evaluable/.test(er.err)], [2, true]);
  assert.deepStrictEqual(r(['-q', '-g', 'main', '-t', 'halt', 'lambda.pl']).out, '[1,4,9]-14\n[x(2),x(3)]\n');
  const w = r(['-g', 'main', '-t', 'halt', 'write.pl']).out.split('\n');
  assert.match(w[0], /^f\(_G\d+,\[1,2\],s,A b,1\+2,\(a:-b,c\)\)$/);
  assert.match(w[1], /^f\(_G\d+,\[1,2\],"s",'A b',1\+2,\(a:-b,c\)\)$/);
  assert.strictEqual(w[2], '- 1');
  assert.match(r(['-g', 'main', '-t', 'halt', 'write.pl']).out, /p\(A\) :-\n {4}q\(A, _\),\n {4}\( {3}r\n {4}-> {2}s\n {4}; {3}t\n {4}\)\.\n/);
  assert.deepStrictEqual(r(['-g', 'main', '-t', 'halt', 'bval.pl']).out, '1\ninference_limit_exceeded\n');
  assert.deepStrictEqual(r(['-g', 'main', '-t', 'halt', 'args.pl', '--', 'x', 'y']).out, '[x,y]\n');
});

test('routes: the picked route gives Prolog\'s answers, and the store keeps the pick', () => {
  const src = 'nrev([], []).\nnrev([H|T], R) :- nrev(T, RT), append(RT, [H], R).\nfib(0, 0).\nfib(1, 1).\nfib(N, F) :- N > 1, A is N-1, B is N-2, fib(A, FA), fib(B, FB), F is FA+FB.\nshow(L) :- format("~w~n", [L]).\n';
  const kept = new Map(); const store = { get: (k) => kept.get(k) || null, set: (k, v) => kept.set(k, v) };
  const goals = ['numlist(1, 200, L), nrev(L, R), R = [X|_]', 'fib(18, F)', 'nrev([a, B, c], R)', 'nrev(L, [1, 2])', 'fib(5, 6)', 'numlist(1, 5, L), nrev(L, R), show(R)'];
  const it = new P.Interpreter({ io: memIO({}), store });
  it.setProgram(src);
  for (const g of goals) {
    const r = it.run(g), r2 = it.run(g);
    P.SWI_WRITE = true; const pr = P.runQuery(P.loadProgram(src), g, { maxAnswers: 1 }); P.SWI_WRITE = false;
    assert.deepStrictEqual([r.answers, r.output], [pr.answers.map((a) => a.text), pr.output], g + ' on ' + r.route);
    assert.deepStrictEqual([r2.answers, r2.output, r2.route], [r.answers, r.output, r.route], g + ': the second run uses the pick');
  }
  assert.ok(kept.size >= goals.length);
  // a new interpreter (a new process) starts from the store
  const it2 = new P.Interpreter({ io: memIO({}), store }); it2.setProgram(src);
  const r3 = it2.run(goals[1]);
  assert.ok(r3.plan.fromStore, 'the pick came from the store');
  assert.ok([...kept.values()].every((v) => v[0] === 't' || v[0] === 'j'));
  const t = [...kept.values()].filter((v) => v[0] === 't');
  for (const v of t) JSON.parse(P.thermo.unpack(P.thermo.fromBase64(v.slice(1)))); // thermo codes decode to the record
});

test('per call: a predicate on the compiled Detlog gives what Prolog gives', () => {
  const src = 'sq(X, Y) :- Y is X * X.\nsums([], 0).\nsums([H|T], S) :- sums(T, S0), sq(H, Q), S is S0 + Q.\nmain :- numlist(1, 60, L), findall(S, (between(1, 60, N), length(P, N), append(P, _, L), sums(P, S)), Ss), sum_list(Ss, T), format("~w~n", [T]).\n';
  const a = swipl({ 'p.pl': src }, ['-g', 'main', '-t', 'halt', 'p.pl']);
  const b = swipl({ 'p.pl': src }, ['-g', 'main', '-t', 'halt', 'p.pl'], { noAccel: true });
  assert.deepStrictEqual(a.out, b.out);
  assert.deepStrictEqual(a.out, '1153510\n');
});

test('compiled C: the C route prints what Prolog prints', (t) => {
  try { cp.execSync('cc --version', { stdio: 'ignore' }); } catch (e) { t.skip('no C compiler'); return; }
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pl2d-interp-'));
  const nativeC = {
    minMs: 0,
    compile(code) { const f = path.join(dir, P.interp.hash(code)); fs.writeFileSync(f + '.c', code); try { cp.execSync('cc -O2 -w -o ' + f + ' ' + f + '.c -lm'); return f; } catch (e) { return null; } },
    run(bin, args) { const t0 = Date.now(); const r = cp.spawnSync(bin, args, { encoding: 'utf8' }); return { stdout: r.stdout, stderr: r.stderr, status: r.status, ms: Date.now() - t0 }; }
  };
  const src = 'nrev([], []).\nnrev([H|T], R) :- nrev(T, RT), append(RT, [H], R).\nqueens(N, Qs) :- numlist(1, N, Ns), permutation(Ns, Qs), safe(Qs).\nsafe([]).\nsafe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).\nno_attack(_, [], _).\nno_attack(Q, [Q1|Qs], D) :- Q =\\= Q1 + D, Q =\\= Q1 - D, D1 is D + 1, no_attack(Q, Qs, D1).\n';
  const it = new P.Interpreter({ io: memIO({}), nativeC }); it.setProgram(src);
  for (const g of ['queens(6, Qs)', 'numlist(1, 300, L), nrev(L, R), R = [X|_]']) {
    const r = it.run(g);
    const c = it.runNativeC(r.plan);
    const pr = P.runQuery(P.loadProgram(src), g, { maxAnswers: 1 });
    assert.deepStrictEqual(c && c.answers.map((a) => a.text), pr.answers.map((a) => a.text), g);
    assert.deepStrictEqual(r.answers, pr.answers.map((a) => a.text), g + ' on ' + r.route);
  }
});

// fixes found running S2A2, mnns and Starlog on the interpreter
test('Starlog, plunit and the fixes from S2A2 and mnns', () => {
  const files = {
    // -div(..): an infix-operator name written as a functor after prefix minus
    'neg.pl': 'main :- K = 3, G = 2, X is -div(-K, G), Y is - mod(7, 4), print(X/Y), nl.\n',
    // plunit: a test chosen by name, and a unit whose condition fails is skipped
    'units.pl': ':- begin_tests(a).\ntest(one) :- true.\ntest(two) :- fail.\n:- end_tests(a).\n:- begin_tests(b, [condition(fail)]).\ntest(no) :- fail.\n:- end_tests(b).\n',
    // a module's initialization/1 calls its own predicates, even when another module exports the same names
    'm1.pl': ':- module(m1, [set/1]).\n:- dynamic d/1.\nset(X) :- assertz(d(X)).\n:- initialization(set(one)).\n',
    'm2.pl': ':- module(m2, [set/1, got/1]).\n:- dynamic d/1.\nset(X) :- assertz(d(X)).\ngot(X) :- d(X).\n:- initialization(set(two)).\n',
    'mods.pl': ':- use_module(m1).\n:- use_module(m2).\nmain :- forall(m1:d(X), writeln(m1-X)), forall(m2:got(Y), writeln(m2-Y)).\n',
    // lists:reverse/2 is the library's even when a module exports reverse/2 that calls it
    'lib.pl': ':- module(r, [reverse/2]).\nreverse(X, Y) :- lists:reverse(X, Y).\n',
    'libuse.pl': ':- use_module(lib).\nmain :- reverse([1,2,3], L), writeln(L).\n',
    // the database is kept from one goal to the next; cyclic terms unify
    'live.pl': ':- dynamic n/1.\nput :- assertz(n(1)).\nshow :- n(X), writeln(X).\ncyc :- X = f(X), Y = f(Y), X = Y, writeln(cyclic_ok).\n',
    // a lambda's own variables are fresh at each call, on every route
    'gcd.pl': 'g(Q, G) :- foldl([_-C, G0, G1]>>(G1 is gcd(G0, abs(C))), Q, 0, G).\nmain :- g([a-4, b-(-6), c-10], G), writeln(G).\n',
    // the empty list as chars or codes is the empty atom or string; read_term gives singletons;
    // is_set/1 compares with ==
    'text.pl': 'main :- string_chars(S, []), atom_chars(A, []), string_codes(T, []), atom_codes(B, []), print([S, A, T, B]), nl,\n' +
      '  term_string(_, "f(X, Y, X, _Z, _)", []), read_term_from_atom(\'g(A1, B1, A1, _C)\', G, [variable_names(Vs)]), length(Vs, NV), print(NV), nl,\n' +
      '  open_string("h(X, Y, X, _Z).", In), read_term(In, _, [singletons(Ss)]), close(In), forall(member(N=_, Ss), writeln(N)),\n' +
      '  ( is_set([a, b, f(_)]) -> writeln(set) ; true ), ( is_set([a, b, a]) -> true ; writeln(not_set) ), ( is_set([X0, Y0]) -> writeln(vars_differ) ; true ), ( is_set([a|_]) -> true ; writeln(partial_not_set) ).\n',
    // hexadecimal digits, with their weights
    'xdigit.pl': "main :- forall(member(C, [a, 'F', '7', g]), ( char_type(C, xdigit(W)) -> format('~w=~w ', [C, W]) ; format('~w:no ', [C]) )), ( code_type(0'c, xdigit(_)) -> writeln(yes) ; writeln(no) ), findall(A-B, nextto(A, B, [1, 2, 3]), Ps), print(Ps), nl.\n"
  };
  const r = (args) => swipl(files, args);
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'neg.pl']).out, '2/ -3\n');
  let x = r(['-g', 'run_tests(a:one)', '-t', 'halt', 'units.pl']);
  assert.strictEqual(x.code, 0); assert.match(x.err, /All 1 tests passed/);
  x = r(['-g', 'run_tests', '-t', 'halt', 'units.pl']);
  assert.strictEqual(x.code, 1); assert.match(x.err, /test a:two: failed/); assert.doesNotMatch(x.err, /b:no/);
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'mods.pl']).out, 'm1-one\nm2-two\n');
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'libuse.pl']).out, '[3,2,1]\n');
  assert.strictEqual(r(['-g', 'put', '-g', 'show', '-g', 'cyc', '-t', 'halt', 'live.pl']).out, '1\ncyclic_ok\n');
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'gcd.pl']).out, '2\n');
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'xdigit.pl']).out, 'a=10 F=15 7=7 g:no yes\n[1-2,2-3]\n');
  assert.strictEqual(r(['-g', 'main', '-t', 'halt', 'text.pl']).out, '["",\'\',"",\'\']\n3\nY\nset\nnot_set\nvars_differ\npartial_not_set\n');
  const conv = P.convert(files['gcd.pl'], { mnn: true, s2a: false, queries: ['g([a-4, b-(-6), c-10], G)'] });
  const q = conv.queries[0], d = P.runDetlogFast(P.loadProgram(conv.text), q.pred, q.vars, {});
  assert.deepStrictEqual(d.answers.map((a) => a.text), ['G = 2']);
});

test('brackets: operator terms and Starlog operators read back as written', () => {
  const ops = ':- op(600, yfx, :).\n:- op(650, yfx, &).\n:- op(650, yfx, >>).\n';
  for (const s of ['X = -div(-K, G)', 'X = - (a)', 'X = (- = a)', 'X = [-]', 'X = -(-)', 'X = \\+mod(a, b)', 'X = (a:b):c', 'X = a:(b:c)', 'X = (a&b)>>c', 'X = - (- 1)', 'X = (:-)', 'X = f((a,b))', 'X = (a|b)']) {
    const prog = P.loadProgram(ops);
    const t = P.readTerm(s).term, txt = P.show(t, { quoted: true });
    assert.ok(P.variantKey(P.readTerm(txt).term) === P.variantKey(t), s + ' -> ' + txt);
    void prog;
  }
});

test('routes: Prolog is kept for a goal where it is at least twice as fast', () => {
  // sub_atom/5 enumerated: the reference engine's own generator, against its answers as rows in converted
  // code (queens/2 used to be the example; answer streams made its converted code the faster route)
  const it = new P.Interpreter({ io: null }); it.setProgram('w(S) :- sub_atom(abcdefghijklmnopqrstuvwxyzabcdefghij, _, _, _, S).\n');
  const r = it.run('findall(S, w(S), L), length(L, N)');
  assert.strictEqual(r.route, 'Prolog'); assert.match(r.why, /at least 2x faster/);
  assert.ok(r.answers[0].endsWith('N = 703'));
  const fib = new P.Interpreter({ io: null }); fib.setProgram('fib(0, 0).\nfib(1, 1).\nfib(N, F) :- N > 1, A is N-1, B is N-2, fib(A, FA), fib(B, FB), F is FA+FB.\n');
  const f = fib.run('fib(21, F)');
  assert.notStrictEqual(f.route, 'Prolog'); assert.deepStrictEqual(f.answers, ['F = 10946']);
});

// The per-call route on answer streams is lazy: a call under once/1 stops after two answers (one to give,
// one to know there are more); asked for more, it runs again for all of them.  Same answers as Prolog.
test('per call: lazy answer streams', () => {
  const prog = ':- dynamic seen/1.\nnat(X) :- between(1, 3000, X).\nfirstbig(L, X) :- nat(X), X > L.\ntwo(L, X) :- nat(X), X > L, X < L + 3.\n' +
    'run(N) :- forall(between(1, N, I), (once(firstbig(I, X)), assertz(seen(X)))).\nrun2(N) :- forall(between(1, N, I), (findall(X, two(I, X), Xs), assertz(seen(Xs)))).\n';
  for (const [g, a] of [['run(60), aggregate_all(count, seen(_), C), seen(Y), Y > 59', 'C = 60, Y = 60'], ['run2(40), aggregate_all(count, seen(_), C), seen([A, B]), A > 38', 'C = 40, A = 39, B = 40']]) {
    const it = new P.Interpreter({ io: null }); it.setProgram(prog);
    const r = it.run(g);
    assert.deepStrictEqual(r.answers, [a], g);
    assert.ok(it.acc && it.acc.streams, 'the per-call route runs stream code');
    assert.ok([...it.acc.info.values()].some(v => v.state === 'jit' && v.jitCalls > 0), 'a predicate ran on the compiled route');
  }
});
