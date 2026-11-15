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
- **Detlog code** is the converted `p__cp` program, run on the deterministic engine (`src/detlog_fast.js`). That engine compiles clauses to closures, selects each clause by its first argument and runs packet loops natively. The C export compiles the same code.
- **MNN Detlog** is the MNN-optimised code on the same engine.

Times are the median of 5 batches after a warm-up, in Node 22. All four engines are written in JavaScript in this app.

| query | Prolog ms | Detlog interpreter ms | interpreter vs Prolog | Detlog code ms | MNN Detlog ms |
| --- | ---: | ---: | ---: | ---: | ---: |
| `fib(18, F)` | 50.7 | 12.6 | 4.0× faster | 161 | 0.45 |
| `numlist(1, 60, L), nrev(L, R)` | 5.89 | 2.31 | 2.5× faster | 27.0 | 24.8 |
| `queens(6, Qs)` | 12.5 | 4.89 | 2.6× faster | 57.0 | 38.3 |
| `pin(A, B, C)` (three spliced generators) | 1.12 | 0.99 | 1.1× faster | 9.55 | 0.073 |
| `anc(X, dee)` | 0.046 | 0.033 | 1.4× faster | 0.18 | 0.035 |
| `classify(0, C)` (cuts) | 0.011 | 0.006 | 1.8× faster | 0.031 | 0.019 |

On the eight examples (52 queries), the interpreter is faster than Prolog on every query in steady state. In the app's own per-run timing, 50 of the 52 come out faster: the other two take microseconds and fall within timer noise.

The converted code is slower than Prolog because it materialises every row as a Prolog list and copies environments. MNN rewrites remove most of that cost where they apply:
- MEMO makes `fib` O(n) instead of O(1.64ⁿ).
- S2A and splice turn data and independent generators into loops.

The sweep `fib(N, F)` for N = 2..18 fits O(1.64ⁿ) for Prolog, the interpreter and Detlog code, which is the golden ratio. MNN Detlog fits O(n).

In the C export, `fib(20, F)` takes 425 ms as plain Detlog code and 1.4 ms as MNN Detlog.

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
| `src/detlog_interp.js` | the Detlog interpreter: the cut-free program run as answer packets, without choicepoints |
| `src/detlog_fast.js` | the deterministic engine for converted Detlog code (closure-compiled, native packet loops) |
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

## Build, test, command line

```sh
node build.js        # builds dist/ and index.html
node test/run.js     # or: npm test
node cli.js examples/fib.pl -q "fib(15, F)" --stats --sweep "fib(N, F)" --values 2..18 \
    --detlog fib_detlog.pl --c fib.c --back fib_back.pl --proof proof.txt
```

## Inputs and outputs

`io/ios.txt` has 200 inputs and outputs from real runs of pl2detlog's functions: Prolog queries on the reference engine, Prolog to Detlog conversion (plain and MNN), conversion and back-conversion, the full analysis (Prolog, Detlog, MNN and back-converted answers, and the proof checks), Newton difference fits, S2A formulas, reading and printing terms, purity, ranges and growth fits. The inputs come from a fixed seed, so the same 200 come out each time. `npm test` runs them again and fails if an output changes; if a change is meant, `npm run ios` writes the new outputs.

BSD-3-Clause.
