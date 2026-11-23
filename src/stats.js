/* pl2detlog stats: static complexity of Prolog vs Detlog, per-query steps / time / choicepoints,
   complexity sweeps with a fitted growth class, and the full analysis pipeline used by the app. */
(function (P) {
  'use strict';
  const { deref } = P;
  const D = deref;

  function prologMetrics(src) {
    const prog = typeof src === 'string' ? P.loadProgram(src) : src;
    const m = { predicates: 0, clauses: 0, facts: 0, rules: 0, goals: 0, cuts: 0, disjunctions: 0, ifThenElse: 0, negations: 0, findalls: 0, nondetCalls: 0, choicePreds: 0, recursive: 0, maxBody: 0, choiceSites: 0, cyclomatic: 1 };
    const calls = new Map();
    for (const k of prog.order) {
      const cls = prog.preds.get(k); if (!cls.length) continue;
      m.predicates++; if (cls.length > 1) { m.choicePreds++; m.cyclomatic += cls.length - 1; }
      const cs = new Set();
      for (const cl of cls) {
        m.clauses++;
        const b = D(cl.body);
        if (b.t === 'a' && b.n === 'true') { m.facts++; continue; }
        m.rules++; let len = 0;
        (function walk(g, top) {
          g = D(g); const gk = P.key(g);
          if (gk === ',/2') { walk(g.a[0], top); walk(g.a[1], top); return; }
          if (top) len++;
          m.goals++;
          if (gk === '!/0') { m.cuts++; return; }
          if (gk === ';/2') { const l = D(g.a[0]); if (l.t === 'c' && l.f === '->') { m.ifThenElse++; m.cyclomatic++; walk(l.a[0], false); walk(l.a[1], false); } else { m.disjunctions++; m.cyclomatic++; walk(g.a[0], false); } walk(g.a[1], false); return; }
          if (gk === '->/2') { m.ifThenElse++; m.cyclomatic++; walk(g.a[0], false); walk(g.a[1], false); return; }
          if (gk === '\\+/1' || gk === 'not/1') { m.negations++; m.cyclomatic++; walk(g.a[0], false); return; }
          if (/^(findall|bagof|setof|aggregate_all|forall)\//.test(gk)) { m.findalls++; walk(g.a[1], false); return; }
          if (P.NONDET_BI.has(gk)) { m.nondetCalls++; m.cyclomatic++; }
          if (prog.preds.has(gk)) cs.add(gk);
        })(cl.body, true);
        m.maxBody = Math.max(m.maxBody, len);
      }
      calls.set(k, cs);
    }
    // recursion via reachability
    for (const k of calls.keys()) { const seen = new Set(); const st = [...calls.get(k)]; let rec = false; while (st.length) { const x = st.pop(); if (x === k) { rec = true; break; } if (seen.has(x)) continue; seen.add(x); for (const y of calls.get(x) || []) st.push(y); } if (rec) m.recursive++; }
    m.choiceSites = m.choicePreds + m.disjunctions + m.nondetCalls;
    return m;
  }
  function detlogMetrics(text) {
    const prog = P.loadProgram(text);
    const m = { predicates: 0, clauses: 0, goals: 0, decisions: 0, auxPredicates: 0, runtimeCalls: 0, packetPreds: 0, choiceSites: 0, maxBody: 0, cyclomatic: 1 };
    const rt = new Set(Object.keys(P.DETLOG_RUNTIME));
    for (const k of prog.order) {
      const cls = prog.preds.get(k); m.predicates++;
      if (/__cp\/\d+$/.test(k)) m.packetPreds++; else m.auxPredicates++;
      if (cls.length > 1) m.cyclomatic += cls.length - 1;
      for (const cl of cls) {
        m.clauses++; let len = 0;
        (function walk(g) { g = D(g); const gk = P.key(g); if (gk === ',/2') { walk(g.a[0]); walk(g.a[1]); return; } len++; m.goals++; if (gk === 'if_commit/3') { m.decisions++; m.cyclomatic++; walk(g.a[0]); walk(g.a[1]); walk(g.a[2]); return; } if (rt.has(gk)) m.runtimeCalls++; })(cl.body);
        m.maxBody = Math.max(m.maxBody, len);
      }
    }
    m.choiceSites = 0;
    return m;
  }

  // run fn repeatedly to time it: returns mean ms per run
  // time fn: warm up (so every engine is measured after JIT compilation), then the median of 5 batches
  function timeIt(fn, budgetMs, maxReps, setup) {
    budgetMs = budgetMs || 30; maxReps = maxReps || 2000;
    const one = () => { const s = setup ? setup() : undefined; const t = P.now(); const r = fn(s); return { dt: P.now() - t, r }; };
    let last = one(); if (last.r && last.r.error) return { ms: last.dt, reps: 1, last: last.r };
    const wall = P.now(); let w = 0; while (P.now() - wall < budgetMs / 6 && w < 50) { one(); w++; } // warm-up
    const est = Math.max(1e-4, (P.now() - wall) / Math.max(1, w));
    const per = Math.max(1, Math.min(maxReps, Math.floor((budgetMs / 6) / est)));
    const batches = [];
    for (let b = 0; b < 5; b++) { let tot = 0; for (let i = 0; i < per; i++) { const x = one(); tot += x.dt; last = x; } batches.push(tot / per); }
    batches.sort((a, b) => a - b);
    return { ms: batches[2], reps: per * 5, last: last.r };
  }

  // growth class from (n, steps) points
  function fitGrowth(pts) {
    pts = pts.filter(p => p.x > 0 && p.y > 0);
    if (pts.length < 3) return { label: 'n/a', k: null };
    const lr = (xs, ys) => { const n = xs.length; const mx = xs.reduce((a, b) => a + b) / n, my = ys.reduce((a, b) => a + b) / n; let sxy = 0, sxx = 0, syy = 0; for (let i = 0; i < n; i++) { sxy += (xs[i] - mx) * (ys[i] - my); sxx += (xs[i] - mx) ** 2; syy += (ys[i] - my) ** 2; } const b = sxx ? sxy / sxx : 0; const r2 = sxx && syy ? (sxy * sxy) / (sxx * syy) : 1; return { b, r2 }; };
    const lx = pts.map(p => Math.log(p.x)), ly = pts.map(p => Math.log(p.y)), x = pts.map(p => p.x);
    const pw = lr(lx, ly), ex = lr(x, ly);
    const spread = Math.max(...pts.map(p => p.y)) / Math.min(...pts.map(p => p.y));
    if (spread < 1.15) return { label: 'O(1)', k: 0, r2: 1 };
    if (ex.r2 > pw.r2 + 0.01 && ex.b > 0.08 && pw.b > 1.5) return { label: 'O(' + Math.exp(ex.b).toFixed(2) + '^n)', k: pw.b, r2: ex.r2, exp: true, base: Math.exp(ex.b) };
    const k = pw.b; let label;
    if (k < 0.2) label = 'O(1)'; else if (k < 0.75) label = 'O(log n) – O(√n)'; else if (k < 1.15) label = 'O(n)'; else if (k < 1.5) label = 'O(n log n)'; else if (k < 2.5) label = 'O(n²)'; else if (k < 3.5) label = 'O(n³)'; else label = 'O(n^' + k.toFixed(1) + ')';
    return { label, k, r2: pw.r2 };
  }
  function parseRange(s) {
    s = String(s || '').trim(); if (!s) return [];
    const m = /^(-?\d+)\s*\.\.\s*(-?\d+)(?:\s*(?:by|step|:)\s*(\d+))?$/.exec(s);
    if (m) { const a = +m[1], b = +m[2], st = +(m[3] || 1); const out = []; for (let i = a; i <= b && out.length < 60; i += st) out.push(i); return out; }
    return s.split(/[\s,]+/).map(Number).filter(n => Number.isFinite(n)).slice(0, 60);
  }

  // ---------- the analysis pipeline ----------
  // opts: { mnn: {fuse, splice, s2a, memo}, sweep: {template, values}, timing: bool, stepLimit }
  function analyse(src, queries, opts) {
    opts = opts || {};
    const res = { errors: [], warnings: [] };
    queries = queries.map(q => q.trim().replace(/\.\s*$/, '')).filter(Boolean);
    const sweepVals = opts.sweep && opts.sweep.template ? parseRange(opts.sweep.values) : [];
    const sweepQs = sweepVals.map(v => opts.sweep.template.replace(/\bN\b|\{N\}|\$N/g, String(v)));
    const allQs = queries.concat(sweepQs);
    const t0 = P.now();
    try { P.loadProgram(src); } catch (e) { res.errors.push(e.message); return res; }
    res.plain = P.convert(src, { mnn: false, queries: allQs });
    res.convertMs = P.now() - t0;
    const t1 = P.now();
    res.mnn = P.convert(src, Object.assign({ mnn: true, queries: allQs }, opts.mnn || {}));
    res.convertMnnMs = P.now() - t1;
    const progPlain = P.loadProgram(res.plain.text), progMnn = P.loadProgram(res.mnn.text);
    let progStream = null, progStreamMnn = null;
    if (res.plain.streamText) { try { progStream = P.loadProgram(res.plain.streamText); } catch (e) { res.errors.push('stream code: ' + e.message); } }
    if (res.mnn.streamText) { try { progStreamMnn = P.loadProgram(res.mnn.streamText); progStreamMnn.pairwiseSource = P.loadProgram(res.mnn.source); } catch (e) { res.errors.push('MNN stream code: ' + e.message); } }
    try { if (progStream) progStream.pairwiseSource = P.loadProgram(res.plain.source); } catch (e) { /* permutes in full */ }
    try { res.backStreams = res.plain.streamText ? P.backConvert(res.plain.streamText) : null; } catch (e) { res.backStreams = null; res.errors.push('back-conversion (streams): ' + e.message); }
    try { res.backStreamsMnn = res.mnn.streamText ? P.backConvert(res.mnn.streamText) : null; } catch (e) { res.backStreamsMnn = null; res.errors.push('back-conversion (MNN streams): ' + e.message); }
    try { progMnn.pairwiseSource = P.loadProgram(res.mnn.source); } catch (e) { /* the JIT then permutes in full */ }
    try { res.backPlain = P.backConvert(res.plain.text); } catch (e) { res.backPlain = null; res.errors.push('back-conversion (plain): ' + e.message); }
    try { res.backMnn = P.backConvert(res.mnn.text); } catch (e) { res.backMnn = null; res.errors.push('back-conversion (MNN): ' + e.message); }
    res.changes = res.backPlain ? P.changeWarnings(src, res.backPlain.text, res.backPlain) : [];
    res.changesMnn = res.backMnn ? P.changeWarnings(src, res.backMnn.text, res.backMnn) : [];
    const backProg = res.backPlain ? safeLoad(res.backPlain.text) : null, backMnnProg = res.backMnn ? safeLoad(res.backMnn.text) : null;
    const lim = opts.stepLimit || 3e6;
    const sharedProg = P.loadProgram(src);
    const dynamic = sharedProg.dynamic.size > 0 || /\b(assert[az]?|retract(all)?)\s*\(/.test(src);
    const runOne = (qi) => {
      const q = res.plain.queries[qi], qm = res.mnn.queries[qi];
      if (q.error) return { query: q.text, error: q.error, prolog: { events: [], answers: [], error: q.error } };
      const r = { query: q.text };
      const fresh = () => P.loadProgram(src); // assert/retract must not leak between runs
      r.prolog = P.runQuery(fresh(), q.text, { stepLimit: lim, maxAnswers: 1000 });
      r.interp = P.runDetlogInterp(res.plain, q.pred, q.vars, { stepLimit: lim * 20 });
      r.plain = P.runDetlogFast(progPlain, q.pred, q.vars, { stepLimit: lim * 20 });
      r.mnn = P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20 });
      if (progStream) r.streams = P.runDetlogFast(progStream, q.pred, q.vars, { stepLimit: lim * 20 });
      if (progStreamMnn) r.streamsMnn = P.runDetlogFast(progStreamMnn, qm.pred, qm.vars, { stepLimit: lim * 20 });
      if (backProg) r.back = P.runQuery(safeLoad(res.backPlain.text), q.text, { stepLimit: lim, maxAnswers: 1000 });
      if (backMnnProg) r.backMnn = P.runQuery(safeLoad(res.backMnn.text), q.text, { stepLimit: lim, maxAnswers: 1000 });
      const ev = JSON.stringify(r.prolog.events);
      r.same = ev === JSON.stringify(r.plain.events) && ev === JSON.stringify(r.mnn.events) && ev === JSON.stringify(r.interp.events) &&
        (!r.streams || ev === JSON.stringify(r.streams.events)) && (!r.streamsMnn || ev === JSON.stringify(r.streamsMnn.events));
      if (opts.timing !== false) {
        const parsedQ = P.readTerm(q.text);
        r.prolog.ms = timeIt(pr => P.runQuery(pr, parsedQ, { stepLimit: lim, maxAnswers: 1000 }), 25, 200, dynamic ? fresh : () => sharedProg).ms;
        r.interp.ms = timeIt(() => P.runDetlogInterp(res.plain, q.pred, q.vars, { stepLimit: lim * 20 })).ms;
        r.plain.ms = timeIt(() => P.runDetlogFast(progPlain, q.pred, q.vars, { stepLimit: lim * 20 })).ms;
        r.mnn.ms = timeIt(() => P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20 })).ms;
        if (r.streams && !r.streams.error) r.streams.ms = timeIt(() => P.runDetlogFast(progStream, q.pred, q.vars, { stepLimit: lim * 20 })).ms;
        if (r.streamsMnn && !r.streamsMnn.error) r.streamsMnn.ms = timeIt(() => P.runDetlogFast(progStreamMnn, qm.pred, qm.vars, { stepLimit: lim * 20 })).ms;
        // against the same algorithm written by hand: MNN Detlog's computation alone, as the reference measures
        if (P.cReference && !r.mnn.error) {
          r.cref = P.cReference(q.text, r.mnn.events);
          if (r.cref) r.mnn.computeMs = timeIt(() => P.runDetlogFast(progMnn, qm.pred, qm.vars, { stepLimit: lim * 20, noDecode: true })).ms;
        }
      }
      return r;
    };
    res.runs = queries.map((_, i) => runOne(i));
    if (sweepVals.length) {
      const pts = sweepVals.map((v, j) => { const r = runOne(queries.length + j); return { n: v, query: sweepQs[j], prolog: r.prolog, interp: r.interp, plain: r.plain, mnn: r.mnn, same: r.same }; });
      const fit = key => fitGrowth(pts.filter(p => !p[key].error).map(p => ({ x: p.n, y: p[key].steps })));
      res.sweep = { template: opts.sweep.template, points: pts, fit: { prolog: fit('prolog'), interp: fit('interp'), plain: fit('plain'), mnn: fit('mnn') } };
    }
    res.metrics = { prolog: prologMetrics(src), plain: detlogMetrics(res.plain.text), mnn: detlogMetrics(res.mnn.text) };
    res.proof = P.prove({ src, plain: res.plain, mnn: res.mnn, backPlain: res.backPlain, backMnn: res.backMnn, backStreams: res.backStreams, backStreamsMnn: res.backStreamsMnn, runs: res.runs });
    // hide sweep queries from the converted text shown to the user? keep them: they are converted like any query
    res.totalMs = P.now() - t0;
    return res;
  }
  function safeLoad(t) { try { return P.loadProgram(t); } catch (e) { return null; } }

  P.prologMetrics = prologMetrics; P.detlogMetrics = detlogMetrics; P.fitGrowth = fitGrowth; P.parseRange = parseRange; P.analyse = analyse; P.timeIt = timeIt;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
