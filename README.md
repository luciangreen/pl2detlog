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
   - *Evaluation*: for every query, the answers, their order, duplicates and output are the same in the source, both Detlog programs and both back-converted programs.
   - *Run-time determinism*: no call had more than one candidate clause.
5. **Shows stats.** For each query it shows steps, time and choicepoints (or Detlog decisions) for Prolog, Detlog and MNN Detlog. It also compares static complexity: predicates, goals, choicepoint sites and cyclomatic complexity. A **complexity sweep** runs a query template for N = a..b and fits a growth class, such as O(n), O(n²) or O(c^n).
6. **Exports:**
   - HTML: a self-contained page that runs the Detlog.
   - Detlog `.pl` with `detlog_runtime.pl` included: consult it in SWI-Prolog and run `?- detlog_run_all.`
   - C, with its runtime.
   - Back-converted Prolog, with the change warnings as comments.
   - The proof report.

## Example: Fibonacci

```prolog
fib(0, 0).
fib(1, 1).
fib(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fib(N1, F1), fib(N2, F2), F is F1 + F2.
```

| `?- fib(15, F).` | steps | time (browser) |
| --- | ---: | ---: |
| Prolog | 6,904 | 7.6 ms |
| Detlog | 90,742 | 71 ms |
| MNN Detlog | 712 | 0.9 ms |

The sweep `fib(N, F)` for N = 2..18 fits **O(1.64ⁿ)** for Prolog and plain Detlog, which is the golden ratio. MNN Detlog fits **O(n)**.

The C export of `fib(20, F)` takes 425 ms as plain Detlog and 1.4 ms as MNN Detlog.

Plain Detlog is slower than Prolog: it copies every environment row and computes complete packets. MNN optimisation is what makes it competitive, and on small list programs Prolog is still faster. The app reports this as it is.

## How Prolog becomes Detlog

| Prolog | Detlog |
| --- | --- |
| facts | `cp_filter(Facts, Args, Rows)` |
| clause `H :- B` | `if_commit(copy_term(Args, H), (code for B, project_rows(...)), Rows = [])` |
| several clauses | clause packets concatenated: `rows_concat/2` |
| `A, B` | `B` mapped over the rows of `A` by a `[]` / `[_|_]` loop predicate |
| `A ; B` | `rows_concat([RowsA, RowsB], Out)` |
| `(C -> T ; E)`, `\+`, `once/1` | the first row of `C`'s packet (`packet_first/3`) selects the branch |
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
- **Errors.** A goal that would raise an error after the first answer of a committed condition still raises it in Detlog, because packets are complete.

## Files

| file | contents |
| --- | --- |
| `index.html`, `dist/index.html` | the app, as one self-contained file (built) |
| `dist/pl2detlog.js` | the library bundle (built) |
| `src/core.js` | terms, reader, printer |
| `src/engine.js`, `src/builtins.js` | reference Prolog engine (the oracle, with step and choicepoint counts) |
| `src/convert.js` | Prolog → Detlog, plain and MNN, with proof steps |
| `src/detlog_engine.js` | deterministic Detlog engine and runtime |
| `src/backconv.js` | Detlog → Prolog and change warnings |
| `src/proof.js` | the independent proof checker |
| `src/stats.js` | metrics, timing, complexity sweeps, the analysis pipeline |
| `src/cgen.js`, `src/runtime.c` | Detlog → C |
| `src/detlog_runtime.pl` | the Detlog runtime for SWI-Prolog (cut-free; `if_commit/3` is its one primitive) |
| `app/` | the app's page and script |
| `cli.js` | command line |
| `examples/` | the example programs |
| `test/run.js` | tests: every example converts, proves, back-converts, compiles to C and runs on the Prolog runtime |

## Build, test, command line

```sh
node build.js        # builds dist/ and index.html
node test/run.js     # or: npm test
node cli.js examples/fib.pl -q "fib(15, F)" --stats --sweep "fib(N, F)" --values 2..18 \
    --detlog fib_detlog.pl --c fib.c --back fib_back.pl --proof proof.txt
```

BSD-3-Clause.
