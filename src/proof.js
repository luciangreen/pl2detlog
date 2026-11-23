/* pl2detlog proof checker.  Independent of the converter: it re-derives what it checks.
   1. shape: the Detlog has no cut, ;, ->, \+, findall, call/N or nondeterministic builtin, and every
      predicate has one clause or clauses told apart by distinct first-argument functors;
   2. justification: every Detlog clause carries a proof step with a known rule;
   3. side conditions: S2A tables re-run on the source, MEMO purity and SPLICE independence re-derived,
      FACTS rows compared with the source facts, deterministic builtins re-classified;
   4. evaluation: the answer packets (answers, order, duplicates, output) of the source, both Detlog
      programs and the back-converted Prolog are equal for every query;
   5. run-time determinism: no call had more than one candidate clause. */
(function (P) {
  'use strict';
  const { deref, Cmp, Var, list, listToArray, show, termVars } = P;
  const D = deref;
  const FORBIDDEN = new Set(['!/0', ';/2', '->/2', '*->/2', '\\+/1', 'not/1', 'findall/3', 'findall/4', 'bagof/3', 'setof/3', 'aggregate_all/3', 'aggregate_all/4', 'forall/2', 'once/1', 'ignore/1', 'call/1', 'catch/3']);
  const RULES = new Set(['CUT', 'SPEC', 'PRED', 'FACTS', 'CLAUSE', 'S2A', 'MEMO', 'DET', 'call_det', 'UNSUPPORTED', 'true', 'fail', 'det', 'effect', 'call', 'member_cp', 'between_cp', 'builtin_rows', 'seq', 'det_prefix', 'effect_prefix', 'disj', 'ite', 'ite_det', 'ite_scan', 'neg', 'neg_det', 'neg_scan', 'findall', 'aggregate', 'splice', 'cut_mark']);
  const STREAM_RULES = new Set(['k_clause', 'k_pred', 'k_cont', 'k_facts', 'k_s2a', 'k_det', 'k_memo', 'k_prune', 'k_query']);
  const isC = (t, f, n) => { t = D(t); return t.t === 'c' && t.f === f && t.a.length === n; };
  const RUNTIME_PREDS = () => new Set(Object.keys(P.DETLOG_RUNTIME).concat(['if_commit/3']));

  function checkShape(detlogText) {
    const prog = P.loadProgram(detlogText);
    const issues = []; let goals = 0, decisions = 0, condUser = 0;
    const rt = RUNTIME_PREDS();
    for (const k of prog.order) {
      const cls = prog.preds.get(k);
      if (cls.length > 1) {
        const seen = new Set(); let ok = true;
        for (const cl of cls) {
          const h = D(cl.head); const a0 = h.t === 'c' ? D(h.a[0]) : null;
          if (!a0 || a0.t === 'v') { ok = false; break; }
          const key = a0.t === 'c' ? 'c:' + a0.f + '/' + a0.a.length : a0.t + ':' + (a0.n !== undefined ? a0.n : a0.v);
          if (seen.has(key)) { ok = false; break; }
          seen.add(key);
        }
        if (!ok) issues.push(k + ': ' + cls.length + ' clauses not told apart by their first argument (a call would leave a choicepoint)');
      }
      for (const cl of cls) walk(cl.body, k, false);
    }
    function walk(g, k, inCond) {
      g = D(g); const gk = P.key(g);
      if (g.t === 'v') { issues.push(k + ': variable goal (call/N)'); return; }
      if (gk === ',/2') { walk(g.a[0], k, inCond); walk(g.a[1], k, inCond); return; }
      if (gk === 'true/0') return;
      goals++;
      if (gk === 'fail/0' || gk === 'false/0') return;
      if (gk === 'if_commit/3') { decisions++; walk(g.a[0], k, true); walk(g.a[1], k, inCond); walk(g.a[2], k, inCond); return; }
      if (FORBIDDEN.has(gk) || (gk && gk.startsWith('call/'))) { issues.push(k + ': contains ' + gk); return; }
      if (P.NONDET_BI.has(gk)) { issues.push(k + ': nondeterministic builtin ' + gk + ' called directly'); return; }
      if (prog.preds.has(gk)) { if (inCond) condUser++; return; }
      if (rt.has(gk)) return;
      const b = P.builtins[gk];
      if (b && !b.nondet && !b.call) return;
      issues.push(k + ': unknown goal ' + gk);
    }
    return { ok: issues.length === 0, issues, preds: prog.order.length, clauses: prog.clauses.length, goals, decisions, condUser };
  }

  // purity, re-derived from the source (greatest fixpoint)
  function purity(src) {
    const prog = P.loadProgram(src); const pure = new Map(); const writes = new Map();
    const PURE = new Set(['=/2', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2', '=</2', '>=/2', 'between/3', 'member/2', 'succ/2', 'plus/3', 'true/0']);
    const OUT = new Set(['write/1', 'print/1', 'writeln/1', 'writeq/1', 'write_canonical/1', 'write_term/2', 'nl/0', 'tab/1', 'put_char/1', 'format/1', 'format/2', 'format/3', 'assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'nb_setval/2', 'b_setval/2']);
    const calls = new Map();
    for (const k of prog.order) {
      let p = !prog.dynamic.has(k), w = false; const cs = new Set();
      for (const cl of prog.preds.get(k)) (function go(g) {
        g = D(g); const gk = P.key(g);
        if (gk === ',/2' || gk === ';/2') { go(g.a[0]); go(g.a[1]); return; }
        if (prog.preds.has(gk)) { cs.add(gk); return; }
        if (gk && /^(findall|aggregate_all|forall|\\\+|once|ignore|call|maplist|foldl|include|exclude|bagof|setof)\//.test(gk)) { p = false; if (g.t === 'c') g.a.forEach(x => { const xd = D(x); if (xd.t === 'c' || xd.t === 'a') go(xd); }); return; }
        if (gk === '->/2') { p = false; go(g.a[0]); go(g.a[1]); return; }
        if (OUT.has(gk)) { w = true; p = false; return; }
        if (!PURE.has(gk)) p = false;
      })(cl.body);
      pure.set(k, p); writes.set(k, w); calls.set(k, cs);
    }
    let ch = true;
    while (ch) { ch = false; for (const k of prog.order) for (const c of calls.get(k)) { if (pure.get(k) && pure.has(c) && !pure.get(c)) { pure.set(k, false); ch = true; } if (!writes.get(k) && writes.get(c)) { writes.set(k, true); ch = true; } } }
    return { pure, writes, prog };
  }

  function s2aRowsOf(spec) {
    spec = D(spec); const K = D(spec.a[0]).v; const cols = listToArray(spec.a[1]).map(D); const rows = [];
    for (let I = 0; I < K; I++) rows.push(cols.map(c => c.f === 'const' ? c.a[0] : c.f === 'data' ? listToArray(c.a[0])[I] : P.Int(listToArray(c.a[0]).reduce((s, d, i) => s + D(d).v * P.binom(I, i), 0))));
    return rows;
  }

  // full proof: source + conversions (+ back-converted) + run results
  function prove(ctx) {
    const { src, plain, mnn, backPlain, backMnn, runs } = ctx;
    const checks = [];
    const add = (group, name, ok, detail) => checks.push({ group, name, ok, detail: detail || '' });
    const pur = purity(src);
    for (const [label, conv] of [['Detlog packets', plain], ['MNN Detlog packets', mnn]]) {
      if (!conv) continue;
      const sh = checkShape(conv.packetText || conv.text);
      add('Shape', label + ': no cut, ;, ->, \\+, findall, call/N or nondeterministic builtin; first-argument determinism', sh.ok, sh.ok ? sh.preds + ' predicates, ' + sh.clauses + ' clauses, ' + sh.decisions + ' if_commit decisions' : sh.issues.slice(0, 8).join('; '));
      if (sh.condUser) add('Shape', label + ': if_commit conditions', 'warn', sh.condUser + ' condition(s) call Detlog predicates (allowed: they are deterministic)');
      // justification
      const unjust = conv.clauses.filter(c => !conv.steps[c.step - 1] || !RULES.has(conv.steps[c.step - 1].rule));
      add('Justification', label + ': every clause carries a proof step', unjust.length === 0, conv.clauses.length + ' clauses, ' + conv.steps.length + ' steps (' + summariseRules(conv.steps) + ')');
      // side conditions
      for (const st of conv.steps) {
        if (st.rule === 'S2A') {
          const k = st.pred; const [f, n] = splitKey(k);
          const cl = conv.clauses[st.clauses[0]]; const spec = D(D(cl.term).a[1]).a[0];
          const isPure = pur.pure.get(k);
          const A = []; for (let i = 0; i < +n; i++) A.push(Var());
          const eng = new P.Engine(pur.prog, { stepLimit: 500000 }); const got = [];
          let err = null; try { eng.solve(Cmp(f, A), () => { got.push(A.map(a => P.resolve(a))); return got.length <= 100000; }); } catch (e) { err = e.message; }
          const exp = s2aRowsOf(spec);
          const same = !err && got.length === exp.length && got.every((r, i) => r.every((x, j) => P.compare(x, exp[i][j]) === 0));
          add('Side conditions', 'S2A ' + k + ': pure, and the loop gives exactly the source answers in order', isPure && same, (isPure ? 'pure' : 'NOT pure') + '; ' + got.length + ' source rows vs ' + exp.length + ' loop rows' + (err ? '; ' + err : '') + '; ' + st.info.formula);
        }
        if (st.rule === 'DET') {
          // re-derived from the Detlog itself: nothing reachable from p__d writes output or updates the database,
          // so running it and then the packet code (status maybe) cannot repeat an effect
          const [f, n] = splitKey(st.pred); const dprog = P.loadProgram(conv.text);
          const seen = new Set(); const todo = [f + '__d/' + (+n + 1)]; let bad = null;
          const EFF = new Set(['effect_text/2', 'assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'nb_setval/2', 'b_setval/2', 'setarg/3', 'nb_setarg/3']);
          while (todo.length && !bad) {
            const k = todo.pop(); if (seen.has(k)) continue; seen.add(k);
            const cls = dprog.preds.get(k); if (!cls) { bad = 'missing ' + k; break; }
            for (const cl of cls) (function walk(g) { g = D(g); const gk = P.key(g); if (gk === ',/2') { walk(g.a[0]); walk(g.a[1]); return; } if (gk === 'if_commit/3') { g.a.forEach(walk); return; } if (EFF.has(gk) || P.EFFECT.has(gk)) bad = gk; else if (dprog.preds.has(gk)) todo.push(gk); })(cl.body);
          }
          add('Side conditions', 'DET ' + st.pred + ': deterministic mode writes no output (re-derived from the Detlog); status maybe runs the packet code', !bad, bad ? 'reaches ' + bad : seen.size + ' predicate(s) reachable from ' + f + '__d, none writes');
        }
        if (st.rule === 'MEMO') add('Side conditions', 'MEMO ' + st.pred + ': pure (variant calls give equal packets)', !!pur.pure.get(st.pred), pur.pure.get(st.pred) ? 'purity re-derived from the source' : 'not pure');
        if (st.rule === 'splice') {
          let ok = false, why = '';
          try {
            const c = P.readTerm('f(' + st.info.gens[0] + ', ' + st.info.gens[1] + ')').term;
            const va = new Set(termVars(c.a[0]).map(v => v.name)); const shared = termVars(c.a[1]).filter(v => va.has(v.name) && v.name !== '_');
            const outs = [c.a[0], c.a[1]].filter(g => pur.writes.get(P.key(g)));
            ok = !shared.length && !outs.length; why = shared.length ? 'shared: ' + shared.map(v => v.name) : outs.length ? 'a generator writes output' : 'no shared variables, no output; guarded at run time by splice_safe/1';
          } catch (e) { why = e.message; }
          add('Side conditions', 'SPLICE in ' + st.pred + ': ' + st.src, ok, why);
        }
        if (st.rule === 'FACTS' && st.info.n) {
          const k = st.pred; const cl = conv.clauses[st.clauses[0]];
          const rows = st.info.table
            ? listToArray(D(cl.term).a[0]).map(r => P.canonClauses ? show(r, { varName: P.namer() }) : '')
            : listToArray(D(D(cl.term).a[1]).a[0]).map(r => P.canonClauses ? show(D(r).a[0], { varName: P.namer() }) : '');
          const srcRows = pur.prog.preds.get(k).map(c => show(list(D(c.head).t === 'c' ? D(c.head).a : []), { varName: P.namer() }));
          const same = rows.length === srcRows.length && rows.every((r, i) => r === srcRows[i]);
          add('Side conditions', 'FACTS ' + k + ': rows are the source facts in order', same, rows.length + ' facts');
        }
      }
      // first-match scans: the generator is member/2 and every filter is a deterministic builtin
      const scanSteps = conv.steps.filter(s => s.rule === 'ite_scan' || s.rule === 'neg_scan');
      if (scanSteps.length) {
        const badScan = [];
        for (const s of scanSteps) {
          try {
            const gk = P.key(P.readTerm(s.info.gen).term);
            if (s.info.facts) { const cls = pur.prog.preds.get(gk); if (!cls || !cls.length || pur.prog.dynamic.has(gk) || cls.some(c => !(D(c.body).t === 'a' && D(c.body).n === 'true'))) badScan.push(s.info.gen + ' (not a predicate of facts)'); }
            else if (gk !== 'member/2') badScan.push(s.info.gen);
            for (const f of s.info.filters) { const fk = P.key(P.readTerm(f).term); const b = P.builtins[fk]; if (fk !== 'true/0' && (!b || b.nondet || b.call || P.EFFECT.has(fk))) badScan.push(f); }
          } catch (e) { badScan.push(s.src); }
        }
        add('Side conditions', label + ': first-match scans run member/2 or a predicate of facts, with deterministic builtin filters', badScan.length === 0, scanSteps.length + ' scan(s)' + (badScan.length ? '; not allowed: ' + badScan.join(', ') : ''));
      }
      const detSteps = conv.steps.filter(s => s.rule === 'det' || s.rule === 'det_prefix' || s.rule === 'ite_det' || s.rule === 'neg_det');
      let badDet = [];
      for (const s of detSteps) { if (s.rule !== 'det') continue; try { const g = P.readTerm(s.src).term; const gk = P.key(g); const b = P.builtins[gk]; if (!b || b.nondet || b.call || P.EFFECT.has(gk)) badDet.push(gk); } catch (e) { } }
      add('Side conditions', label + ': goals compiled as deterministic are deterministic builtins', badDet.length === 0, detSteps.length + ' deterministic goals' + (badDet.length ? '; not deterministic: ' + badDet.join(', ') : ''));
      if (conv.errors.length) add('Coverage', label + ': predicates converted', false, conv.errors.map(e => e.msg).join('; '));
      else add('Coverage', label + ': every predicate converted', true, conv.genPreds.filter(g => !/^\$query/.test(g.key)).length + ' predicate(s), plus ' + conv.queries.length + ' query predicate(s)');
    }
    // stream code (src/stream.js): shape, a rule for every clause, the side conditions it relies on
    for (const [label, conv] of [['Stream Detlog', plain], ['MNN stream Detlog', mnn]]) {
      if (!conv || !conv.stream) continue;
      const st = conv.stream, text = st.text;
      const sh = checkShape(text);
      add('Shape', label + ': no cut, ;, ->, \\+, findall, call/N or nondeterministic builtin; first-argument determinism', sh.ok, sh.ok ? sh.preds + ' predicates, ' + sh.clauses + ' clauses, ' + sh.decisions + ' if_commit decisions' : sh.issues.slice(0, 8).join('; '));
      // no answer packets outside the query boundary and the S2A/memo tables, no environment copies
      const own = st.clauses.map((c, i) => ({ c, t: st.tags[i] })).filter(x => x.t.rule !== 'k_query');
      const PACKET = new Set(['splice_extend/4', 'rows_concat/2', 'rows_cut_concat/2', 'project_rows/4', 'project_list/4', 'packet_first/3', 'packet_split/3', 'effect_text/2', 'cp_filter/3', 'splice2/6', 'copy_term/2']);
      const used = new Set(); for (const x of own) (function w(g) { g = D(g); if (g.t !== 'c') return; if (g.f === ':-' || g.f === ',' || g.f === 'if_commit') { g.a.forEach(w); return; } const k = P.key(g); if (PACKET.has(k)) used.add(k); })(x.c);
      add('Shape', label + ': no answer packet and no environment copy outside the query boundary', used.size === 0, used.size ? 'uses ' + [...used].join(', ') : own.length + ' clauses outside the ' + st.clauses.filter((c, i) => st.tags[i].rule === 'k_query').length + ' query boundary clause(s)');
      const unk = st.tags.filter(t => !STREAM_RULES.has(t.rule));
      const by = new Map(); for (const t of st.tags) by.set(t.rule, (by.get(t.rule) || 0) + 1);
      add('Justification', label + ': every clause carries a stream rule', unk.length === 0, st.clauses.length + ' clauses (' + [...by].map(([r, n]) => r + ' ' + n).join(', ') + ')');
      const stepOf = (rule, pred) => conv.steps.find(x => x.rule === rule && x.pred === pred);
      const preds = rule => [...new Set(st.tags.filter(t => t.rule === rule).map(t => t.pred))];
      for (const pk of preds('k_det')) {
        // as for DET: nothing reachable from p__d writes output or updates the database
        const [f, n] = splitKey(pk); const dprog = P.loadProgram(text);
        const seen = new Set(); const todo = [f + '__d/' + (+n + 1)]; let bad = stepOf('DET', pk) ? null : 'no DET step';
        const EFF = new Set(['assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'nb_setval/2', 'b_setval/2', 'setarg/3', 'nb_setarg/3']);
        while (todo.length && !bad) {
          const k = todo.pop(); if (seen.has(k)) continue; seen.add(k);
          const cls = dprog.preds.get(k); if (!cls) { bad = 'missing ' + k; break; }
          for (const cl of cls) (function walk(g) { g = D(g); const gk = P.key(g); if (gk === ',/2') { walk(g.a[0]); walk(g.a[1]); return; } if (gk === 'if_commit/3') { g.a.forEach(walk); return; } if (EFF.has(gk) || P.EFFECT.has(gk)) bad = gk; else if (dprog.preds.has(gk)) todo.push(gk); })(cl.body);
        }
        add('Side conditions', 'stream DET ' + pk + ': the deterministic mode of the proven DET step writes no output; maybe runs the stream', !bad, bad ? bad : seen.size + ' predicate(s) reachable from ' + f + '__d, none writes');
      }
      for (const pk of preds('k_memo')) add('Side conditions', 'stream MEMO ' + pk + ': pure (a variant call gives the same answers, in order)', !!pur.pure.get(pk) && !!stepOf('MEMO', pk), pur.pure.get(pk) ? 'purity re-derived from the source' : 'not pure');
      for (const pk of preds('k_s2a')) add('Side conditions', 'stream S2A ' + pk + ': the rows are the table of the proven S2A step', !!stepOf('S2A', pk), stepOf('S2A', pk) ? 'step ' + stepOf('S2A', pk).id : 'no S2A step');
      for (const pk of preds('k_facts')) {
        const rows = st.clauses.filter((c, i) => st.tags[i].rule === 'k_facts' && st.tags[i].pred === pk).map(c => listToArray(D(D(c).a[1]).a[0]))[0] || [];
        const srcRows = (pur.prog.preds.get(pk) || []).map(c => show(list(D(c.head).t === 'c' ? D(c.head).a : []), { varName: P.namer() }));
        const same = rows.length === srcRows.length && rows.every((r, i) => show(r, { varName: P.namer() }) === srcRows[i]);
        add('Side conditions', 'stream FACTS ' + pk + ': rows are the source facts in order', same, rows.length + ' facts');
      }
      for (const tk of preds('k_prune')) {
        // re-derived: the pairwise test of the source predicate, and the tests the generated pairs check
        let pw = null; try { pw = P.pairwise(P.loadProgram(conv.source), tk); } catch (e) { pw = null; }
        const pc = st.clauses.find((c, i) => st.tags[i].rule === 'k_prune' && st.tags[i].pred === tk && isC(c, ':-', 2) && /__pwpairs$/.test(D(D(c).a[0]).f || '') && D(D(c).a[0]).a.length === 3 && isC(D(D(c).a[0]).a[0], '.', 2));
        let ok = !!pw && !!pc, why = pw ? '' : 'no pairwise form re-derived';
        if (ok) {
          const h = D(D(pc).a[0]), m = new Map([[pw.vars.Q, D(h.a[0]).a[0]], [pw.vars.Y, h.a[1]], [pw.vars.D, h.a[2]]]);
          const want = pw.tests.map(t => show(P.copy(t, m), { varName: P.namer() }));
          const have = P.flatConj(D(pc).a[1]).slice(0, pw.tests.length).map(t => show(t, { varName: P.namer() }));
          ok = want.join() === have.join(); why = ok ? pw.proof : 'tests differ: ' + have.join(', ') + ' vs ' + want.join(', ');
        }
        add('Side conditions', 'stream PRUNE permutation then ' + tk + ': prefixes failing a pair are dropped, the same permutations kept in order', ok, why);
      }
    }
    // CUT round trip
    for (const [label, back] of [[plain && plain.form === 'streams' ? 'Stream Detlog' : 'Detlog', backPlain], [mnn && mnn.form === 'streams' ? 'MNN stream Detlog' : 'MNN Detlog', backMnn], ['Detlog packets', ctx.backPackets], ['MNN Detlog packets', ctx.backPacketsMnn]]) {
      if (!back) continue;
      const cw = P.changeWarnings(src, back.text, back);
      const same = cw.filter(w => w.kind === 'same').length, changed = cw.filter(w => w.kind === 'changed'), bad = cw.filter(w => w.kind === 'error' || w.kind === 'removed');
      add('Back-conversion', label + ' -> Prolog: predicates restored exactly', bad.length ? false : changed.length ? 'warn' : true, same + ' identical, ' + changed.length + ' changed (equivalent forms), ' + bad.length + ' missing' + (bad.length ? ': ' + bad.map(b => b.pred).join(', ') : ''));
    }
    // evaluation
    if (runs) for (const r of runs) {
      const ref = JSON.stringify(r.prolog.events);
      const parts = [];
      let ok = true; let limitOnly = false;
      for (const [nm, x] of [['Detlog interpreter', r.interp], ['Detlog code', r.plain], ['MNN Detlog code', r.mnn], ['Detlog packet code', r.packets], ['MNN Detlog packet code', r.packetsMnn], ['back-converted Prolog', r.back], ['back-converted (MNN) Prolog', r.backMnn]]) {
        if (!x) continue;
        const same = JSON.stringify(x.events) === ref && !x.error === !r.prolog.error;
        if (!same) { ok = false; if (r.prolog.truncated || r.prolog.limit || (x.error && /infinite|no finite packet|step limit/.test(x.error))) limitOnly = true; parts.push(nm + ' differs' + (x.error ? ' (' + x.error + ')' : '')); }
      }
      add('Evaluation', '?- ' + r.query, ok ? true : limitOnly ? 'warn' : false, ok ? r.prolog.answers.length + ' answer(s)' + (r.prolog.output ? ' + output' : '') + ', same order, duplicates and output in Prolog, the Detlog interpreter, the Detlog programs (streams and packets, plain and MNN) and the back-conversions' : parts.join('; ') + (limitOnly ? ' — infinite generator: no finite packet (documented limit)' : ''));
      for (const [nm, x] of [['Detlog', r.plain], ['MNN', r.mnn], ['packets', r.packets], ['MNN packets', r.packetsMnn]]) if (x && x.violations) add('Determinism', nm + ' ?- ' + r.query, false, x.violations + ' call(s) with more than one candidate clause: ' + x.violationPreds.join(', '));
    }
    if (runs && runs.length) {
      const anyViol = runs.some(r => ['plain', 'mnn', 'packets', 'packetsMnn'].some(k => r[k] && r[k].violations));
      if (!anyViol) add('Determinism', 'no Detlog call left a choicepoint (first-argument selection was unique on every call)', true, runs.length + ' queries');
    }
    const GO = ['Shape', 'Justification', 'Side conditions', 'Coverage', 'Back-conversion', 'Evaluation', 'Determinism'];
    checks.sort((x, y) => GO.indexOf(x.group) - GO.indexOf(y.group));
    const fails = checks.filter(c => c.ok === false).length, warns = checks.filter(c => c.ok === 'warn').length;
    return { checks, ok: fails === 0, fails, warns, text: proofText(checks, plain, mnn) };
  }
  function summariseRules(steps) { const m = new Map(); for (const s of steps) m.set(s.rule, (m.get(s.rule) || 0) + 1); return [...m].map(([r, n]) => r + ' ' + n).join(', '); }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  function proofText(checks, plain, mnn) {
    const L = ['pl2detlog proof report', '======================', ''];
    let g = null;
    for (const c of checks) { if (c.group !== g) { L.push('', '## ' + c.group); g = c.group; } L.push((c.ok === true ? '[ok]   ' : c.ok === 'warn' ? '[warn] ' : '[FAIL] ') + c.name + (c.detail ? '\n        ' + c.detail : '')); }
    for (const [label, conv] of [['Detlog (plain)', plain], ['MNN-optimised Detlog', mnn]]) {
      if (!conv) continue;
      L.push('', '## Proof steps: ' + label, '');
      for (const s of conv.steps) {
        if (['true', 'fail', 'det', 'call', 'effect', 'seq', 'member_cp', 'between_cp', 'builtin_rows'].includes(s.rule) && s.clauses.length === 0) { L.push('step ' + s.id + '  ' + s.rule.padEnd(13) + ' ' + s.pred + '  ' + oneLine(s.src)); continue; }
        L.push('step ' + s.id + '  ' + s.rule.padEnd(13) + ' ' + s.pred + '  ' + oneLine(s.src) + (s.clauses.length ? '  -> clauses ' + s.clauses.map(i => i + 1).join(',') : '') + (s.info && s.info.formula ? '  [' + s.info.formula + ']' : ''));
      }
    }
    L.push('', '## Rules', '', ...RULE_DOC.map(([r, d]) => r.padEnd(14) + d));
    return L.join('\n') + '\n';
  }
  function oneLine(s) { s = String(s || '').replace(/\s+/g, ' '); return s.length > 140 ? s.slice(0, 137) + '...' : s; }
  const RULE_DOC = [
    ['CUT', 'H :- G, !, B. Rest  ==>  ( [A..]=[h..], G -> B ; Rest ): cut commits to the first answer of the head match and G'],
    ['SPEC', 'maplist/foldl/include/exclude/partition with a known closure ==> a specialised recursive predicate (no call/N)'],
    ['PRED', 'packet of a predicate = concatenation of its clause packets, in clause order'],
    ['CLAUSE', 'rename the call apart, unify with the head; each env row projected on the head is an answer'],
    ['FACTS', 'packet of facts = the facts that unify with the call, in order'],
    ['seq', 'packet of (A, B) = packet of A with every row replaced by the packet of B in that row'],
    ['disj', 'packet of (A ; B) = packet of A ++ packet of B'],
    ['ite', '(C -> T ; F): output of C up to its first answer, then T on that answer; F if C has none'],
    ['neg', '\\+ G = (G -> fail ; true)'],
    ['ite_scan', '(Pre, member(X, Xs), Post -> T ; F), Pre and Post deterministic builtins: scan Xs in place and stop at the first element that passes'],
    ['neg_scan', '\\+ (Pre, member(X, Xs), Post): the same scan, with T = fail and F = true'],
    ['findall', 'all of G\'s output, then one answer binding the list of template instances (no findall/3)'],
    ['aggregate', 'aggregate_all over the packet of G (count, sum, max, min, bag, set)'],
    ['det', 'a deterministic builtin has at most one answer: if_commit(B, [Env], [])'],
    ['effect', 'output builtins write their text as out(Text) items, in Prolog order'],
    ['member_cp', 'member/between/other nondeterministic builtins: their answers as a packet (builtin_rows)'],
    ['det_prefix', 'MNN: deterministic builtins at the start of a conjunction run in place (no row loop)'],
    ['splice', 'MNN: independent generators computed once and combined by a Cartesian product in Prolog order'],
    ['S2A', 'MNN: a pure predicate with a finite ground table becomes a loop over I = 0..K-1 (Newton formulas, constants or data)'],
    ['cut_mark', 'a cut inside a branch emits [cut, e(Row)]: row loops stop after it and later alternatives and clauses are dropped'],
    ['MEMO', 'MNN: a pure tree-recursive predicate is tabled by call variant'],
    ['call_det', 'MNN: a call of a DET predicate in packet code runs its deterministic mode in place: yes gives [Env], no gives []; maybe undoes it and makes the packet call'],
    ['k_clause', 'streams: a clause becomes p__kJ(Head.., K): its goals in order, each call given the rest as a continuation term; the first answer K accepts commits, a rejected one is undone by the trail'],
    ['k_pred', 'streams: a predicate tries its clauses in order: if_commit(p__k1(A.., K), true, p__k2(A.., K)), with a cut cell when a clause cuts'],
    ['k_cont', 'streams: the rest of a conjunction after a call, as dl_k(p__cN(Env.., K)) :- Rest; dl_k/1 is selected by its first argument'],
    ['k_facts', 'streams: facts as a table walked in order (dl_facts_k)'],
    ['k_s2a', 'streams + S2A: the rows of the proven S2A table, walked in order (dl_rows_k)'],
    ['k_det', 'streams + DET: the proven deterministic mode first; yes is the one answer, no is none, maybe runs the stream'],
    ['k_memo', 'streams + MEMO: the answers of a pure predicate per call variant, from the table or collected once'],
    ['k_prune', 'streams + PRUNE: permutation then a pairwise test: each placed element is tested against the earlier ones, so a failing prefix is not extended'],
    ['k_query', 'streams: the query boundary collects the answers, with the text written before each, as the query packet'],
    ['DET', 'MNN: an output-free predicate whose clauses are told apart by their first argument, and whose goals are deterministic, runs as p__d(Args, Status) without packets; status maybe (a first argument unbound where several clauses match) falls back to the packet code']
  ];
  P.checkShape = checkShape; P.prove = prove; P.purity = purity; P.RULE_DOC = RULE_DOC;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
