# pl2detlog

pl2detlog converts Prolog to **Detlog**: Prolog without cut, `;`, `->`, `\+`, `findall/3`, `call/N` or any other construct that leaves or prunes a choicepoint. It runs in the browser.

It is a web app in the style of [pl2js](https://github.com/luciangreen/pl2js), separate from LucianOS. The Detlog it writes follows [detlog2](https://github.com/luciangreen/detlog2): every predicate `p/n` becomes `p__cp/n+1`, which succeeds exactly once with its **answer packet**.

Open `index.html` (or `dist/index.html`) in a browser. No server or install is needed.

## The SWI-Prolog module: install and use

`prolog/pl2detlog.pl` is a module for SWI-Prolog, separate from the web app. It:

- converts a Prolog program to readable **Detlog** and **Detlog MNN**, in new folders next to the program's;
- compiles a query to an **executable in the fastest of the three forms** (Prolog, Detlog, Detlog MNN).

It needs only SWI-Prolog 9 or later, with no packages and no Node. It was tested on SWI-Prolog 11.1.0.

### Install

As a pack, from SWI-Prolog:

```prolog
?- pack_install(pl2detlog, [url('https://github.com/luciangreen/pl2detlog.git')]).
?- use_module(library(pl2detlog)).
```

From a clone, without installing:

```sh
git clone https://github.com/luciangreen/pl2detlog.git
swipl pl2detlog/app/pl2detlog.pl compile prog.pl -g main      # command line
```

```prolog
?- use_module('pl2detlog/prolog/pl2detlog').                   % or load it in SWI-Prolog
```

### Use

From the command line (as a pack, `swipl pl2detlog ...`; from a clone, `swipl path/to/app/pl2detlog.pl ...`):

```sh
swipl pl2detlog convert prog.pl                          # writes prog_detlog/ and prog_mnn/
swipl pl2detlog convert prog.pl -q "queens(8, Qs)"       # converted for this query's modes
swipl pl2detlog compile prog.pl                          # main/0 or initialization(main, main)
swipl pl2detlog compile prog.pl -g main -o prog          # name the main predicate
swipl pl2detlog compile prog.pl -q "queens(8, Qs), print(Qs), nl" -o queens8
./queens8
```

From SWI-Prolog:

```prolog
?- pl2detlog_convert('prog.pl', []).
?- pl2detlog_convert('prog.pl', [query("queens(8, Qs)"), form(mnn)]).
?- pl2detlog_compile('prog.pl', [main(main), exe(prog)]).
?- pl2detlog_compile('prog.pl', [query("queens(8, Qs), print(Qs), nl"), exe(queens8)]).
?- pl2detlog_check('prog.pl', [query("fib(21, F)")], Results).   % time and compare, no build
```

`compile` prints, for example:

```
% form      time per run      output
% prolog    3.550 ms          same as Prolog
% detlog    18.902 ms         same as Prolog
% mnn       98.60 us          same as Prolog
% fastest: mnn
% built /home/me/fib (mnn form)
```

**When to name the main predicate.** `compile` runs the program's `initialization(main, main)` goal or its `main/0`. If it has neither, give `-g Name` or `-q "Goal"`. `-q` takes any goal, so it can compile a query such as `queens(8, Qs), print(Qs), nl`. The executable runs the goal's first answer once, as `swipl -g Goal` does. `convert` needs no query, but with one the modes are known and more of the program stays deterministic (see "Limits" below).

| option (Prolog) | command line | meaning |
| --- | --- | --- |
| `main(Name)` | `-g Name`, `--main Name` | the main predicate |
| `query(Goal)` | `-q Goal`, `--query Goal` | the query: a goal, as text or a term |
| `form(F)` | `--form F` | `detlog`, `mnn` or `both` (default), for `convert` |
| `out(Dir)` | `--out Dir` | the output folder (default: next to the program, see below) |
| `exe(Path)` | `-o Path` | the executable (default: the program's name without `.pl`) |
| `forms(List)` | `--forms prolog,mnn` | the forms that `compile` times (default: all three) |
| `budget(Seconds)` | `--budget S` | the time spent timing each form (default 0.5) |

### What it writes

For `prog.pl` and every file it loads by a relative path (`include/1`, `consult/1`, `ensure_loaded/1`, `use_module/1,2`, `[...]`), it writes two folders:

- the common folder of all those files is the root;
- the folders are `<root>/prog_detlog/` and `<root>/prog_mnn/`;
- each keeps the program's folder structure, so a relative `include` or `use_module` across folders still finds its file. An absolute path to a program file is moved into the new folder.

Each folder holds:

- the converted files;
- `detlog_rt.pl`, the runtime that the files load;
- `PROOFS.txt`, the rules applied to each predicate and the side conditions that were checked.

Comments and directives are kept. The code is laid out as Prolog, with clauses and goals one per line, and variables keep their source names. Each changed predicate gets one comment line, for example `% MNN memo: ...`, so each predicate can be read against the original. `test/prolog/multi/` is a program in three folders.

A predicate whose clauses are told apart by a bound argument stays as it was written, with unnecessary cuts dropped:

```prolog
% source                                   % Detlog MNN
no_attack(_, [], _).                       no_attack(_, [], _).
no_attack(Q, [Q1|Qs], D) :-                no_attack(Q, [Q1|Qs], D) :-
    Q =\= Q1 + D, Q =\= Q1 - D,                Q=\=Q1+D,
    D1 is D + 1,                               Q=\=Q1-D,
    no_attack(Q, Qs, D1).                      D1 is D+1,
                                               no_attack(Q, Qs, D1).
```

A necessary cut becomes `if_commit/3`. Head unifications that only bind outputs move after the decision:

```prolog
max(X, Y, X) :- X >= Y, !.                 max(X, Y, Z) :-
max(_, Y, Y).                                  if_commit(X>=Y, Z=X, Z=Y).
```

A nondeterministic predicate `p/N` becomes `p__all/N+2`, a difference list of its answers in Prolog's order. Its first answer is `p__first/N`. Builtin generators followed by tests are one lazy loop:

```prolog
queens(N, Qs) :-                           queens__first(N, Qs) :-
    numlist(1, N, Ns),                         numlist(1, N, Ns),
    permutation(Ns, Qs),                       dl_fused_first(permutation(Ns, Qs), safe(Qs)).
    safe(Qs).
```

### The three forms and the rules

- **Prolog**: the program as written.
- **Detlog**: the program without cut, `;`, `->`, `\+`, `findall/3` or `call/N`. `if_commit/3` is the one decision construct. When `detlog_rt` is loaded it is compiled inline as `(C -> T ; E)`, so it costs nothing at run time.
  - *Modes*: one call pattern per predicate (ground, fresh variable or anything, for each argument) is found by abstract interpretation, starting from the query.
  - *CUT*: a cut is dropped when its guard is deterministic and no later clause can match the same call. Any other cut becomes `if_commit/3`. `\+`, `once/1`, `ignore/1`, if-then-else and `forall/2` are written with `if_commit/3`.
  - *DET*: a predicate whose clauses exclude each other for its call pattern, and whose goals all have at most one answer, keeps its name and its clauses. Its clauses are told apart by a ground argument (SWI-Prolog indexes it) or by an `if_commit/3` chain.
  - *ALL and FIRST*: a nondeterministic predicate gets `p__all` and `p__first`. A conjunction after a nondeterministic goal is a loop over its answers. A first-answer scan stops at the first answer the rest accepts, so later answers are never tested, as in Prolog.
  - *SPEC*: `maplist/2..5`, `foldl/4..6`, `include/3`, `exclude/3` and `partition/4` with a known closure (yall lambdas included) become recursive predicates. `findall/3,4`, `aggregate_all/3`, `bagof/3` and `setof/3` (without free variables) are read off the answer list.
- **Detlog MNN**: Detlog plus these MNN rewrites:
  - *guards*: clauses told apart by complementary tests (`X < 0` / `X >= 0`, `N > 1` against `fib(0, _)`) are deterministic;
  - *MEMO*: a pure, deterministic, tree-recursive predicate called with ground inputs is tabled. `fib/2` becomes linear;
  - *accumulate*: `p([], []). p([H|T], R) :- p(T, RT), append(RT, E, R).` becomes `p(L, R) :- p__acc(L, [], R)`, by the associativity of `append`. `nrev/2` becomes linear;
  - *UNFOLD*: a call of a one-clause predicate whose body is pure builtins is replaced by that body;
  - *FUSE*: a builtin generator whose conjunction continues with builtins and deterministic goals is enumerated lazily by the runtime (`dl_fused_first/2`, `dl_fused_all/5`). The answers and their order are the same, and no answer list is built;
  - *facts as data*: the answers of a nondeterministic predicate of facts are `dl_match(Facts, Call, ...)`;
  - first answers of a goal followed only by goals that cannot fail (`write/1`, `X is E`, ...) call `p__first` directly.

**Proofs, sparingly.** The code carries one comment line per rewrite. The proof stays out of the code: `PROOFS.txt` lists each rule with the side conditions that were checked for each predicate. `compile` and `pl2detlog_check/3` also run the query in all three forms, each in a fresh process, and keep a form only if its output and success are Prolog's.

**Choosing the form and building.** Each form runs the query in a fresh process for about `budget` seconds, and the fastest form that gave Prolog's output is built. The build is `swipl -o Exe --stand_alone=true -c` on that form's files. The executable needs SWI-Prolog's shared library at run time, as any SWI-Prolog saved state does.

Microseconds per run on this machine (`swipl test/prolog/bench.pl`, SWI-Prolog 11.1.0; small differences are noise):

| query | Prolog µs | Detlog µs | Detlog MNN µs | MNN ÷ Prolog | fastest |
| --- | ---: | ---: | ---: | ---: | --- |
| `fib(21, F)` | 2666 | 16926 | 91.2 | 0.03 | MNN |
| `fib(25, F)` | 34882 | 140104 | 123 | 0.004 | MNN |
| `numlist(1, 300, L), nrev(L, R)` | 1394 | 1457 | 110 | 0.08 | MNN |
| `numlist(1, 2000, L), doubles(L, D), total(D, S)` | 480 | 352 | 354 | 0.74 | Detlog / MNN |
| `queens(8, Qs)`, first answer | 2569 | 87212 | 3030 | 1.18 | Prolog |
| `queens(6, Qs)`, all answers | 911 | 1608 | 959 | 1.05 | Prolog |
| `pin(A, B, C)`, all answers | 209 | 1144 | 204 | 0.97 | MNN |
| `anc(X, dee)`, all answers | 6.8 | 25.3 | 19.5 | 2.87 | Prolog |

Plain Detlog is slower than Prolog wherever there is search. It builds every answer list in full and copies the environment for each answer, where Prolog backtracks. MNN takes that cost away where a rewrite applies (MEMO, accumulate, FUSE, UNFOLD), and is otherwise about as fast as Prolog. For small nondeterministic queries such as `anc/2`, Prolog stays fastest, and `compile` builds the Prolog form.

### Limits

- **Modes.** Each predicate has one call pattern, the least upper bound of all its calls. A predicate called with a bound argument in one place and an unbound one in another is converted for "anything" in both.
- **Interface without a query.** With no query, every predicate that nothing calls is the program's interface, and is converted for calls in any mode. Every other predicate is converted for the modes the program calls it with. If its converted form has no version under its own name, it is also written as it was (`% as written too, ...`), so every predicate can still be called by name. With a query, only the query is the interface, and a predicate that the query does not use is written as it was.
- **Answer lists are complete.** A nondeterministic predicate computes all its answers when the caller needs them as a list. If a later answer raises an error or never ends, so does the converted code, even where Prolog would have stopped earlier. Scans and FUSE are the exceptions. When a builtin generator has no end (`between(0, inf, X)`, `repeat`):
  - the predicate is written as it was where it is called by name;
  - MNN's FUSE enumerates it lazily, as Prolog does;
  - an answer list of it raises `detlog_infinite_answers` instead of running for ever.
- **Kept as Prolog.** These predicates are written as they were:
  - a cut inside `;` or `->` that cuts the clause (the web app converts these with cut markers);
  - `*->`;
  - dynamic predicates.

  A nondeterministic predicate with side effects is converted for its first answers. Where its answers are needed one by one, it runs as an ordinary Prolog conjunction inside `dl_once/1`, so the output keeps Prolog's order.
- **Lambdas.** A yall lambda's free variables are taken to be bound when it is called, as they are in `Free/[X]>>Goal`.
- **Modules.** The program is converted as one namespace. A module's export list gains the `__first` and `__all` versions of the predicates it exports.
- **C.** The C route (`--c`, `--run`) is in the Node command line (`cli.js`); the SWI-Prolog module compiles to SWI-Prolog executables.

### Tests

```sh
swipl test/prolog/run_tests.pl            # 200 cases + the three-folder program
swipl test/prolog/run_tests.pl --record   # write test/prolog/ios.txt again
swipl test/prolog/bench.pl                # the timing table above
```

The 200 cases are:

- the app's 63 example queries, each run for all answers and for the first;
- 74 value sweeps: `fib/2` for 0..24, `nrev/2` for lengths 0..19, `queens/2` solution counts for 1..8, `classify/2` for -3..11, and `doubles/2`/`total/2` for lengths up to 5000.

Each case runs in all three forms, each in a fresh process. It passes when the three agree and the output equals the pair recorded in `test/prolog/ios.txt` from a real run. Two more checks run after the 200 cases:

- the multi-folder program in `test/prolog/multi/` gives the same output and has mirrored folders;
- each of the nine examples, converted with no query, loads and answers its first query as Prolog does.

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

## The interpreter: SWI-Prolog programs on the Detlog MNN and C route

`bin/pl2detlog-run.js` takes a `swipl` command line and runs it without SWI-Prolog (`src/interp.js`). Each goal that converts runs on one route: the intersection of Detlog MNN and C. That is the proved MNN program, with its C tier for the predicates that compile to C:

```sh
node bin/pl2detlog-run.js -g main -t halt proofs/updates.pl      # as: swipl -g main -t halt proofs/updates.pl
node bin/pl2detlog-run.js --explain -g "queens(8, Qs), print(Qs), nl" -t halt queens.pl
```

| Route | What runs | Used when |
| --- | --- | --- |
| Detlog MNN and C | The proved Detlog MNN rewrite, run by the JIT, with the C tier for every predicate whose modes compile to C (as JavaScript in a page, `C (JS)`; plain `MNN` when no predicate compiles). On Node, a goal that takes 5 ms or more also runs as the C export, compiled with `cc` (or `$CC`), and that binary is kept. | The conversion is exact and, on the first run, its answers and output equal Prolog's. |
| Prolog | The reference engine, with SWI-Prolog's library (`src/swi.js`). | The goal uses what only Prolog keeps exact (files and streams, `assert`, messages), the conversion has errors, the routes disagree, or Prolog is at least twice as fast on this goal (and at least 0.5 ms faster). Inside it, a predicate that is called often can run on the compiled Detlog instead. Its first calls run both ways, the answers and output must be the same, and the faster way is kept. Predicates that look at variables themselves (`==`, `var/1`, `copy_term/2`, ...) stay on Prolog. |

**Why one route.** The interpreter used to time every route on a goal's first run and keep the fastest. On the 25 bundled example goals, the Detlog MNN and C route was the fastest, or within 5% of it, on 23. Its total was 1.62 ms against 1.58 ms for the fastest route of each goal, and MNN without the C tier took 110 ms. Timing every route made the first runs about 20% slower (963 ms against 801 ms in all). So the first run now runs the Detlog MNN and C route once and checks its answers against Prolog once. That check also times Prolog. When Prolog looks faster, a short goal is run twice more each way, because first runs include compiling. Prolog is kept for the goal if it takes half the time or less, and is at least 0.5 ms faster. A long goal (over 200 ms) is decided on its first runs.

| Goal (ms per run, after the first) | MNN | MNN + C tier | Compiled C | Prolog | Route kept |
|---|---|---|---|---|---|
| nrev 300 | 0.43 | 0.25 | 2.5 | 112 | Detlog MNN |
| fib 21 | 0.39 | 0.023 | 2.8 | 12.6 | MNN + C tier |
| sum of 1..200,000 | 2,180 | 2,028 | – | 1,768 | MNN + C tier (Prolog isn't 2x faster) |
| queens 6, all solutions | 185 | 74 | 26 | 19.7 | Prolog (now about 11 ms a run, was 64) |

On the 63 bundled example goals, the MNN + C tier route totals 2.2 ms, Prolog 8.0 ms and MNN alone 6.1 ms. None of them is 0.5 ms faster on Prolog, so all stay on the Detlog routes. The combined route remembers the results of pure predicates within a run, which is why fib is so fast.

**First run and later runs.** The first run of a goal picks its route. The choice and the conversion go into a store: `$PL2DETLOG_CACHE` (default `~/.cache/pl2detlog`), or the browser's storage in a page. The next process starts from the store. Compiled C programs are kept there too.

**The store and the thermodynamic compression MNN.** Text in the store (the conversion and the choice) is kept as thermodynamic compression codes (`src/thermo.js`), a port of mnns's `prolog/thermo/thermo.pl`. A sequence is stored as its symbol counts and its rank among all sequences with those counts. That rank fits in exactly ceil(log2 M) bits for a class of M sequences, so no lossless code for the class is shorter. Each position's neuron adds M·(c1+…+c(i−1))/N to the rank. Decoding finds a position's symbol from one quotient: q = ⌊R·N/M⌋ lies in its count block. A record is kept in this form only when it is smaller and decoding it is not slower than doing the conversion again; otherwise it is kept as JSON. `P.thermo.prove` checks round trip, bijection, neuron sum and the entropy bound on every sequence of a finite domain, as `thermo_prove/3` does.

**SWI-Prolog compatibility** (`src/swi.js`):
- dicts and `Dict.key` / `.put(...)`;
- JSON (`atom_json_dict`, `json_read_dict`, `json_write_dict`, ...);
- strings in every mode;
- streams and files (`open`, `read_term`, `read_line_to_string`, `tmp_file_stream`, ...) and standard input;
- modules: private predicates are renamed per module, exported ones are forwarded, `Module:Goal` works, and files can be loaded while the program runs;
- yall lambdas, `format/2,3` (with `~W`, `~e`, column stops), `portray_clause/1` laid out as SWI-Prolog does, and write/print/writeq with SWI-Prolog's spacing;
- `b_setval/2` undone on backtracking, `call_with_inference_limit/3`, `call_with_time_limit/2`, `limit/2`, `findnsols/4`, assoc, `ord_*`, `option/2,3` and `gensym`;
- Unicode letters and symbol characters, `=@=`, operators as operands (`is/2`), `op/3` and module-exported operators;
- `halt/1` exit codes, `initialization/1,2`, and swipl's messages for a goal that fails or raises an error.

**Starlog and load-time expansion.** `term_expansion/2` and `goal_expansion/2` are applied while files load, as SWI-Prolog applies them, including in files loaded while the program runs (`expand_term/2` and `expand_goal/2` too). Starlog's operators are read and written with the brackets they need. Everything in Starlog runs on the interpreter: Visual Starlog's examples, its 51 `tests/test_*.pl` files, and the 18 plunit units of `tests/run_tests.pl`. plunit is built in: `begin_tests/1,2` (unit conditions included), `run_tests/0,1` (a unit, `Unit:Test`, or a list), and the test options `true(..)`, `fail`, `throws(..)`, `error(..)`, `all(..)` and `set(..)`.

**When SWI-Prolog is still used.** A program can need what only SWI-Prolog has: it defines `term_expansion/4`/`goal_expansion/4` or `prolog_load_file/2`, calls a predicate that is not defined or built in, or has a syntax error the reader doesn't accept. The command line checks for these before running anything. When `swipl` is installed it hands the same arguments over (`--no-swipl` turns this off). In a web page it runs on the interpreter regardless.

**How close it is to SWI-Prolog.** MNN in Action (`mnnaction`) drives all of mnns and S2A2 through `swipl`. Its 44 demo runs were recorded on SWI-Prolog. On the interpreter, all 44 give byte-identical JSON. mnns's S2A2 bridge tests pass (18 of 18), and so do the 34 tests of S2A2's `fold_tests.pl` (in 5 s). Getting there fixed these:
- `copy_term/2` no longer marks a term ground when it keeps one of its variables shared (yall's `Free/Lambda`);
- the database and global variables are kept from one goal to the next, so what `initialization/1` asserts, `-g main` sees;
- a module's `initialization/1` calls the module's own predicates;
- `-div(X, Y)` is read as minus applied to `div(X, Y)`;
- `lists:reverse/2` and other library-qualified calls reach the library, even when a module exports the same name;
- cyclic terms unify, and bindings of variables newer than the last choicepoint are not trailed (as in the WAM);
- of two variables, the newer is bound to the older;
- a lambda's own variables are fresh at each call on the Detlog route too;
- per-call compiled Detlog is skipped for calls on large terms, and it is checked against Prolog again on calls 2, 4, 8 and so on;
- `term_variables/2` and `ground/1` visit each shared subterm once (S2A2's tuple strategy builds terms with much sharing);
- `run_tests(Unit:Test)` runs that one test.

The command line has no step or time limit, as `swipl` has none; `PL2DETLOG_TIME_LIMIT` (seconds) sets one. Output is written as the goals make it. LucianOS's and Lucian Office's proof programs (`proofs/*.pl`) prove all their theorems and match all 200 recorded runs.

**Speed.** On these programs the interpreter is slower than SWI-Prolog: the Prolog route is a JavaScript engine. For example, `updates.pl`'s 13 exhaustive theorems take about 8 s. The faster routes pay off where a goal converts: compiled C, the JIT, and the rewrites in "Engines and speed".

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
| `src/interp.js` | the interpreter: routes per goal and per call, the store, swipl command lines, loading SWI-Prolog files and modules |
| `src/swi.js` | SWI-Prolog's library for the reference engine (dicts, JSON, streams, modules, ...) |
| `src/thermo.js` | the thermodynamic compression MNN (from mnns) and the store's codec |
| `bin/pl2detlog-run.js` | `swipl` command lines on the interpreter (Node): compiled C, the store on disk, hand-over to swipl |
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
| `test/interp.test.js` | thermo (examples, proof, store), SWI-Prolog programs, routes and the store, per-call routes, compiled C |
| `test/algebra.test.js` | each rewrite against the Prolog engine, and the C export and JIT with and without them |
| `prolog/pl2detlog.pl` | the SWI-Prolog module: Prolog to Detlog and Detlog MNN, modes, determinism, the rewrites, the writer, and `compile` |
| `prolog/detlog_rt.pl` | the runtime that converted files load (`if_commit/3`, answer lists, fused loops) |
| `prolog/pl2detlog_bench.pl` | runs a query in a fresh process for `compile`: its output once, then its time per run |
| `app/pl2detlog.pl` | the module's command line (`swipl pl2detlog ...` when installed as a pack) |
| `pack.pl` | the SWI-Prolog pack description |
| `test/prolog/` | the module's 200 cases (`run_tests.pl`, `ios.txt`), the three-folder program (`multi/`) and `bench.pl` |

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
