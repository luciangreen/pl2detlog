# pl2detlog

pl2detlog converts Prolog to **Detlog**: Prolog without cut, `;`, `->`, `\+`, `findall/3`, `call/N` or any other construct that leaves or prunes a choicepoint. It runs in the browser.

It is a web app in the style of [pl2js](https://github.com/luciangreen/pl2js), separate from LucianOS. The Detlog it writes follows [detlog2](https://github.com/luciangreen/detlog2): every predicate `p/n` becomes `p__cp/n+1`, which succeeds exactly once with its **answer packet**.

Open `index.html` (or `dist/index.html`) in a browser. No server or install is needed.

## What it does

1. **Converts Prolog to Detlog.** Nondeterministic predicates become cut-free functions that return all their answers as data. `findall/3`, `aggregate_all/3`, `\+`, if-then-else and `once/1` are written as packet predicates, not as calls to `findall`. The output's only decision construct is `if_commit/3`. Each predicate has one clause, or clauses told apart by their first argument, so a call never leaves a choicepoint.
2. **Optimises with MNN rewrites (MNN Detlog).** Each rewrite can be switched off in the app.
   - *det_prefix*: deterministic builtins run in place.
   - *splice*: independent generators are computed once and combined as a Cartesian product.
   - *S2A*: pure predicates with a finite table become loops over Newton formulas, constants or data.
   - *MEMO*: pure tree-recursive predicates are tabled by call variant.
   - *DET*: an output-free predicate whose clauses are told apart by one argument, and whose goals are deterministic, also gets a packet-free version `p__d(Args, Status)`. It runs Prolog's own clause selection and body in place and answers `yes`, `no` or `maybe`. `maybe` means the index argument was unbound where several clauses match; the packet code then runs. Calls between DET predicates never build packets. A call of a DET predicate from packet code (*call_det*) binds the environment in place, and undoes that on `maybe`.
   - *Scans over facts*: a committed condition over a predicate of facts reads only up to the first fact that matches, as `member/2` scans do.
   - *Identity projection and call-through*: a clause whose environment is exactly its head arguments returns its rows without projecting them. `h(X..) :- q(X..)` returns `q`'s packet.
3. **Converts Detlog back to Prolog, with change warnings.** It works from the Detlog text alone, so you can edit the Detlog and convert it back.
   - Cuts are restored from the `if_commit/3` chains.
   - `maplist/foldl/include/exclude/partition` closures, including yall lambdas, are folded back.
   - S2A loops become formulas or facts.
   - Every predicate that differs from your source is listed with a diff and the reason.
4. **Checks a proof.** The checker is independent of the converter. It checks:
   - *Shape*: there are no forbidden constructs, and calls are deterministic by first argument.
   - *Justification*: every clause carries a proof step with a known rule.
   - *Side conditions*: these are re-derived. S2A tables are re-run on the source, purity is re-derived for MEMO, independence and no-output for splice, and facts are compared.
   - *Evaluation*: for every query, the answers, their order, duplicates and output are the same in the source, the Detlog interpreter, both Detlog programs and both back-converted programs.
   - *Run-time determinism*: no call had more than one candidate clause.
5. **Shows stats.** For each query it shows steps, time and choicepoints (or Detlog decisions) for Prolog, the Detlog interpreter, Detlog code and MNN Detlog. It also compares static complexity: predicates, goals, choicepoint sites and cyclomatic complexity. A **complexity sweep** runs a query template for N = a..b and fits a growth class, such as O(n), O(n²) or O(c^n).
6. **Exports:**
   - HTML: a self-contained page that runs the Detlog.
   - Detlog `.pl` with `detlog_runtime.pl` included: consult it in SWI-Prolog and run `?- detlog_run_all.`
   - C, with its runtime.
   - Back-converted Prolog, with the change warnings as comments.
   - The proof report.

## Engines and speed

The app runs every query on four engines and checks that they all give the same answer packet.

- **Prolog** runs on the reference engine: ordinary cut and backtracking semantics. It is the oracle every conversion is checked against.
- **The Detlog interpreter** (`src/detlog_interp.js`) is detlog2's choicepointless, cutless interpreter. It runs the cut-free program (rule CUT applied, closures specialised) as answer packets:
  - Clauses are compiled once into closures.
  - Heads are matched WAM-style, without copying.
  - A call computes the callee's packet and splices it into the conjunction row by row, undoing bindings between rows. No choicepoint is ever created.
  - Runs of deterministic goals execute in place.
  - `(C -> T ; E)`, `\+` and `once/1` take the first row of `C` and never demand the rest.
  - A cut inside a branch is a status that stops the remaining rows and clauses.
- **Detlog code** is the converted `p__cp` program, run on the deterministic engine (`src/detlog_fast.js`). That engine compiles the program to JavaScript source, one function per predicate:
  - arguments are positional and clause variables are JS locals;
  - heads are matched inline, and each clause is selected by its first argument;
  - `if_commit/3` is a labelled block;
  - integer arithmetic and comparisons run natively, and anything else falls back to the builtin;
  - `copy_term/2` into fresh variables is an assignment;
  - packet loops are native loops;
  - a `member/2` or `permutation/2` generator spliced into an environment is one loop, fused with the row loop that consumes it. When that loop's rows are filtered by a DET predicate, the filter runs on each solution in place, and only kept rows are copied.

  Step counts and clause selection are those of the closure compiler, which remains the fallback. The C export compiles the same code.
- **MNN Detlog** is the MNN-optimised code on the same engine, plus its **native tier**. A DET predicate `p__d` entered with ground inputs and fresh output variables is compiled, for that mode, from its own Detlog to a JavaScript function, roughly the C program for it:
  - ground terms in, outputs returned;
  - no logic variables, no trail, no unification of unbound terms;
  - integers as raw numbers (unboxed arguments, and unboxed results where every return is an integer);
  - direct calls between native functions;
  - memoisation of tabled calls in a plain map.

  Anything the analysis can't follow means no native function for that mode. Anything unexpected at run time (a non-integer in arithmetic, a zero divisor, a deep stack) bails out to the generic code, which then gives the answer or the error. The code is pure, so nothing can run twice observably. A native call counts as one step, so MNN step counts are lower than the generic code's.

All times are microseconds per run, in Node 22 and `cc -O2`, recorded by `node bench/compare.js` (`bench/results.json`):
- The JavaScript engines are warmed up and run in batches for about 300 ms each.
- **C** (`bench/reference.c`) and **JavaScript** (`bench/reference.js`) are the same algorithms written directly by hand. They use the same order of solutions, linked lists for lists, and no memoisation.
- **MNN Detlog (JIT)** is MNN Detlog's run without formatting its answers as text, which is what the references measure. The Prolog, interpreter and Detlog-code columns include formatting.
- **The C export** (`cc -O2`) times itself the same way: `./prog -r N` repeats each query, with the memory of each repetition released.

| query | C µs | JavaScript µs | Prolog µs | Detlog interpreter µs | Detlog code µs | MNN Detlog (JIT) µs | MNN Detlog, C export µs | JIT ÷ C | C export ÷ C |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `fib(18, F)` | 2.95 | 23.8 | 24,649 | 5,073 | 72,179 | 8.43 | 2.60 | 2.9× | 0.9× |
| `fib(21, F)` | 15.7 | 97.0 | 138,608 | 22,820 | 313,338 | 8.34 | 4.00 | 0.5× | 0.3× |
| `numlist(1, 60, L), nrev(L, R)` | 5.19 | 11.7 | 2,001 | 1,353 | 12,222 | 36.7 | 17.1 | 7.1× | 3.3× |
| `numlist(1, 300, L), nrev(L, R)` | 161 | 290 | 90,321 | 23,552 | 310,666 | 798 | 476 | 4.9× | 2.9× |
| `numlist(1, 2000, L), doubles(L, D), total(D, S)` | 11.0 | 26.7 | 6,446 | 239,084 | 184,160 | 186 | 106 | 17× | 9.6× |
| `queens(6, Qs)` | 8.23 | 31.3 | 16,227 | 3,869 | 12,111 | 281 | 133 | 34× | 16× |
| `queens(7, Qs)` | 62.2 | 371 | 89,192 | 34,375 | 113,275 | 2,116 | 1,006 | 34× | 16× |
| `pin(A, B, C)` | 0.51 | 1.30 | 785 | 398 | 3,295 | 3.35 | 4.10 | 6.6× | 8.0× |
| `anc(X, dee)` | <0.01 | 0.24 | 16.0 | 6.57 | 67.6 | 3.08 | 3.60 | — | — |

**Why plain converted code is slower than Prolog.** It is Detlog's representation, not its semantics. The interpreter runs the same choicepoint-free, cut-free semantics and is faster than Prolog on these queries (except `doubles`/`total`, where its `maplist` path is slow). Converted code is slower because it materialises every answer set as a list of rows, copies environments at every call, and keeps every variable as a heap logic variable with trail entries, even in deterministic integer code.

**What MNN removes.**
- MEMO makes `fib` linear, so MNN `fib(21)` is faster than the exponential C.
- S2A and splice turn data and independent generators into loops.
- DET and the native tier run deterministic predicates as typed functions. This covers `nrev`, `queens`'s `safe/1`, `classify` and the `maplist`, `foldl`, `include` and `partition` specialisations.
- Fusion runs generate-and-test without building the generated packet.

**Against hand-written code.** Apart from `fib`, which MEMO makes faster than both references, MNN Detlog's C export is within 2.9–16× of the hand-written C, and the JIT within 2.6–9× of the hand-written JavaScript. The exception is `anc(X, dee)`: its C takes nanoseconds, and MNN's cost is the fixed per-query cost of 2–3 µs. The remaining gap is term allocation: a C term is a 72-byte cell, and every solution of `permutation/2` is built as a list so that it can be an answer.

**In the app**, the results show **% of C's speed**: the same algorithm's time written by hand in C, over MNN Detlog's time (100% is as fast as C). It appears per query and as a mean, for the benchmark algorithms, and only when the reference's answers are exactly the program's. The app can't compile C, so it times the hand-written JavaScript in the browser and scales that by the C ÷ JavaScript ratio measured for that algorithm (`src/cref.js`). The C tab gives the C export's recorded %.

**The C export reads its own % of C's speed.** For a query that runs one of the benchmark algorithms (and whose answers are exactly the hand-written version's), the generated program includes the hand-written C from `bench/reference.c`. After the query it times that in the same process and prints, for example, `% hand-written C (queens): 0.0076 ms per run; this program runs at 7.98% of C's speed`. Use `./prog -r N` for a steady figure; the step limit applies per run. `node cli.js prog.pl -q QUERY --c prog.c --run [REPS]` builds and runs it, picking the repetitions when REPS is left out.

**Unchecked by default.** The native tier (the C route, in JavaScript and in the C export) assumes its type contract and tests nothing at run time: no type tests on its inputs, no ground test at entry (C), no overflow or zero-divisor tests, and no step limit in the C export. A call outside the contract (a float where an integer is expected, a result beyond 2^53 in JavaScript or 2^63 in C) can give a wrong answer. Set `P.DETLOG_CHECKED = true`, or build the C with `--checked` (`-DDL_CHECKED`), to test everything and bail out to the generic code, which then gives Prolog's answer or error.

**The C export's data and loops.** A term is 40 bytes, with a compound's arguments in the same allocation; integers from -1024 to 65535 are shared; builtins are found by name with a two-character test first. `permutation/2` tested by a native predicate with no outputs writes each permutation into the same list cells and calls the native function directly; only kept permutations are built and copied. The program prints its startup time (`% startup`). `--best` builds the MNN program and the plain one (no determinism rewrites), times each as a whole process (startup and one run) and per run, and keeps the faster.

**Rewrites from first principles (MNN).** Before conversion, `src/rewrite.js` rewrites the Prolog where an algebraic identity makes it cheaper; each rewrite's derivation is in `conv.algebra` and in the C file's header, and `{ algebra: false }` turns them off.

- *Accumulate an appended result.* `p([], []). p([H|T], R) :- p(T, RT), append(RT, E, R).` computes p(L) = p(T) ++ E. With acc(L, A) = p(L) ++ A, acc([], A) = A and acc([H|T], A) = acc(T, E ++ A) by the associativity of ++, and p(L) = acc(L, []). So `nrev` becomes linear for a proper list; any other list runs the original clauses.
- *Solve for the last generator.* `between(Lo, Hi, X), E1 =:= E2`, with the test linear in X with coefficient ±1 and its other variables integers bound earlier, has exactly one candidate: `X is S, Lo =< X, X =< Hi` (also through a one-clause `d(X) :- between(0, 9, X)`).
- *Fuse a map into the fold that reads it.* `maplist(F, L, D), foldl(G, D, A0, S)` (or one-clause wrappers of them), with F and G single `is/2` clauses and A0 a number, is one walk `mf(L, D, A0, S)` by induction on the list: same answers, order and errors, since G's `is/2` on numbers cannot fail or raise. D is still built. Queries are fused too.
- *Prune a pairwise test* (`src/algebra.js`). A test t(L) of the form `t([X|Xs]) :- r(X, Xs, C0), t(Xs)` with `r` comparing X with each later element at distance d holds iff every pair (Li, Lj), i < j, passes at distance C0 + (j − i − 1). The condition is closed under prefixes, so `permutation(Xs, Ys), t(Ys)` need not extend a failing prefix: the C export and the JIT (when it is given the source as `prog.pairwiseSource`, as the app does) build only the prefixes that pass, and keep the same permutations in the same order.

**The C export's data, in more detail.** Ground compound constants in the code are built once at startup and shared (unification never writes into a term without variables). An S2A table's rows are built once, outside the per-run memory, and a call with unbound or ground arguments only selects matching rows. Cells over ground parts are marked ground when they are made, so copying and resolving stop at them; the native tier marks its cells ground outright, since its outputs are ground by its contract. A list cell is 48 bytes. Native recursions whose last step is a self call (directly, or after placing a list cell whose tail is the call's output) are written as tail calls, which the C compiler makes into loops. `=/2`, `var/1`, `nonvar/1`, `==/2`, `\==/2` and `copy_term/2` are written in place; a head argument that is a new variable is the caller's argument itself. Memory released between timing runs is kept for the next run.

Per run, against the hand-written C in `bench/reference.c` (µs, `cc -O2`, this machine; noisy):

| query | hand-written C | C export | |
| --- | ---: | ---: | --- |
| `fib(21, F)` | 17 | 1.8 | faster (memo) |
| `fib(18, F)` | 3.0 | 1.7 | faster |
| `numlist(1, 300, L), nrev(L, R)` | 170 | 12.7 | faster (accumulate) |
| `numlist(1, 60, L), nrev(L, R)` | 5.6 | 2.5 | faster |
| `queens(7, Qs)` | 67 | 19–25 | faster (pairwise pruning) |
| `queens(6, Qs)` | 8.8 | 3.6 | faster |
| `pin(A, B, C)` | 0.56 | < 0.1 | faster (solve, S2A rows kept) |
| `numlist(1, 2000, L), doubles(L, D), total(D, S)` | 11.8 | 15–17 | 1.2–1.5× slower |
| `anc(X, dee)` | 0.003 | 0.3 | slower |

The two still slower are where the hand-written C does less work than the query asks for. For `doubles`/`total` it uses 16-byte cells of raw integers, where the export builds Prolog terms (48-byte cells and shared integer terms) for the `L` and `D` it prints. `anc` is three comparisons in a static array in C, with no answer terms; the export builds the three answer bindings. Both are within the fixed cost of producing Prolog answers, not a search the export does more of.

**Integers are unbounded**, as in SWI-Prolog: the reference engine keeps a JavaScript number while an integer is a safe integer and a BigInt beyond (`fact(30, F)` gives `F = 265252859812191058636308480000000`). The JIT's inline arithmetic and the native tier work on raw numbers only while every result stays a safe integer; any other result bails out to the generic code, so the answers are the same. In the C export, `+`, `-` and `*` in native functions check for overflow and bail out.

**The C export** has the same native tier as the JIT. The JS engine runs the queries once, and every (predicate, mode) its native tier compiled is compiled to C as well: `long long` integers, outputs through pointers, `longjmp` to bail out, memo tables keyed by integers. It also has the JIT's generate-and-test fusion. Its runtime allocates a compound in one block, shares ground subterms when copying, and clears the memo table in proportion to what was stored.

**On all nine examples (63 queries) in steady state,** MNN Detlog takes 0.70× Prolog's time (geometric mean). The queries where it is still slower are small nondeterministic ones (1–24 µs), where building packets costs more than Prolog's backtracking.

**Minimising the generated code** (`node bench/minimise.js`) would merge only 11 of 735 generated predicates (Moore-style: equal up to renaming of variables and called predicates), and 24 are forwarders. The generated predicates are not redundant as states. The redundancy is in the data flow, which fusion and the native tier remove.

The sweep `fib(N, F)` for N = 2..18 fits O(1.64ⁿ) for Prolog, the interpreter and Detlog code, which is the golden ratio. MNN Detlog fits O(n).

In the C export, `fib(20, F)` takes 133 ms as plain Detlog code and 3 µs as MNN Detlog.

## How Prolog becomes Detlog

| Prolog | Detlog |
| --- | --- |
| facts | `cp_filter(Facts, Args, Rows)` |
| clause `H :- B` | `if_commit(copy_term(Args, H), (code for B, project_rows(...)), Rows = [])`; when the head arguments are distinct variables the renaming cannot fail, so it is just `copy_term(Args, H), code for B, project_rows(...)` |
| several clauses | clause packets concatenated: `rows_concat/2` |
| `A, B` | `B` mapped over the rows of `A` by a `[]` / `[_|_]` loop predicate |
| `A ; B` | `rows_concat([RowsA, RowsB], Out)` |
| `(C -> T ; E)`, `\+`, `once/1` | the first row of `C`'s packet (`packet_first/3`) selects the branch |
| the same with `C = (Pre, member(X, Xs), Post)`, `Pre` and `Post` deterministic builtins (also a cut local to `findall/3`) | one scan predicate `q(Xs, e(Env), O) :- if_commit(Xs = [Y\|Ys], if_commit((X = Y, Post), T, q(Ys, e(Env), O)), E)` that stops at the first element passing `Post` (rules `ite_scan`, `neg_scan`) |
| `findall/3`, `aggregate_all/3`, `setof/3` | the packet itself (`packet_split/3`, `project_list/4`) |
| `H :- G, !, B.` followed by other clauses | one clause `( [A..] = [h..], G -> B ; ... )` (rule CUT) |
| a cut inside a branch | a `cut` marker: row loops stop after it and later clauses are dropped |
| `member/2`, `between/3`, `append/3`, ... | `builtin_rows(Goal, Rows)` |
| MNN: an output-free predicate with argument-exclusive clauses and deterministic goals | `p__cp` runs `p__d(Args, Status)` in place; status `maybe` runs the packet code `p__cpx` (rule DET) |
| `write/1`, `format/2`, ... | `out(Text)` items, in Prolog order |
| `maplist(F, ...)`, `foldl`, `include`, lambdas | a specialised recursive predicate (rule SPEC) |

Detlog2 rejects a cut inside an if-then-else branch. pl2detlog converts it with cut markers.

## Limits

- **Infinite generators.** A generator with infinitely many answers, such as `between(1, inf, X)`, has no finite packet. Converted code reports this instead of answering.
- **`call/N` with an unbound closure** cannot be converted.
- **`bagof/setof` that group by free variables** cannot be converted (add `^`, or use `findall`). `catch/3` is converted without catching.
- **Errors.** A goal that would raise an error after the first answer of a committed condition still raises it in Detlog, because packets are complete. The exception is a condition of the form `(Pre, member(X, Xs), Post)` with deterministic builtins around `member/2`: it is scanned, and elements after the first match are never tested, as in Prolog. For example, `firsts([2, a], F)` in `examples/scan.pl` gives `F = [2]` rather than a type error.

## Files

| file | contents |
| --- | --- |
| `index.html`, `dist/index.html` | the app, as one self-contained file (built) |
| `dist/pl2detlog.js` | the library bundle (built) |
| `src/core.js` | terms, reader, printer |
| `src/engine.js`, `src/builtins.js` | reference Prolog engine (the oracle, with step and choicepoint counts) |
| `src/convert.js` | Prolog → Detlog, plain and MNN, with proof steps |
| `src/rewrite.js` | MNN source rewrites from first principles (accumulate, solve for the last generator, map/fold fusion), each with its derivation |
| `src/algebra.js` | pairwise prefix-closed tests (the pruned permutation loop of the C export and the JIT) |
| `src/detlog_interp.js` | the Detlog interpreter: the cut-free program run as answer packets, without choicepoints |
| `src/detlog_fast.js` | the deterministic engine for converted Detlog code: compiled to JavaScript source (JIT), with the closure compiler as fallback, and the native tier for DET predicates |
| `src/native.js` | the native tier's compiler, shared by the JIT (JavaScript) and the C export (C) |
| `src/cref.js` | the benchmark algorithms written by hand, for the app's % of C's speed |
| `bench/` | `compare.js` against hand-written C (`reference.c`) and JavaScript (`reference.js`); `minimise.js` measures DFA minimisation of the generated code |
| `src/detlog_engine.js` | the reference Detlog engine and the Detlog runtime |
| `src/backconv.js` | Detlog → Prolog and change warnings |
| `src/proof.js` | the independent proof checker |
| `src/stats.js` | metrics, timing, complexity sweeps, the analysis pipeline |
| `src/cgen.js`, `src/runtime.c` | Detlog → C |
| `src/detlog_runtime.pl` | the Detlog runtime for SWI-Prolog (cut-free; `if_commit/3` is its one primitive) |
| `app/` | the app's page and script |
| `cli.js` | command line |
| `examples/` | the example programs |
| `test/run.js` | tests: every example converts, proves, back-converts, compiles to C and runs on the Prolog runtime |
| `io/` | 200 inputs and outputs from real runs (`io/ios.txt`, `io/ios.jsonl`), made from `io/cases.mjs` |
| `test/ios.test.js` | runs the 200 inputs again and checks the outputs are the same |
| `test/algebra.test.js` | each rewrite against the Prolog engine, and the C export and JIT with and without them |

## Build, test, command line

```sh
node build.js        # builds dist/ and index.html
node test/run.js     # or: npm test
node cli.js examples/fib.pl -q "fib(15, F)" --stats --sweep "fib(N, F)" --values 2..18 \
    --detlog fib_detlog.pl --c fib.c --back fib_back.pl --proof proof.txt
node cli.js examples/queens.pl -q "queens(7, Qs)" --c queens.c --run   # build, run, % of C's speed
```

## Inputs and outputs

`io/ios.txt` has 200 inputs and outputs from real runs of pl2detlog's functions: Prolog queries on the reference engine, Prolog to Detlog conversion (plain and MNN), conversion and back-conversion, the full analysis (Prolog, Detlog, MNN and back-converted answers, and the proof checks), Newton difference fits, S2A formulas, reading and printing terms, purity, ranges and growth fits. The inputs come from a fixed seed, so the same 200 come out each time. `npm test` runs them again and fails if an output changes; if a change is meant, `npm run ios` writes the new outputs.

BSD-3-Clause.
