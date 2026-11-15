/* pl2detlog app: wires the editor, the analysis pipeline, the result views and the exports. */
(function () {
  'use strict';
  const P = window.PL2D;
  const $ = id => document.getElementById(id);
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const fmt = n => n == null || !isFinite(n) ? '—' : n >= 1e6 ? (n / 1e6).toFixed(2) + 'M' : n >= 1e4 ? (n / 1e3).toFixed(1) + 'k' : String(Math.round(n));
  const ms = n => n == null ? '—' : n < 0.01 ? '<0.01' : n < 10 ? n.toFixed(3) : n.toFixed(1);
  const store = { get(k) { try { return localStorage.getItem('pl2detlog:' + k); } catch (e) { return null; } }, set(k, v) { try { localStorage.setItem('pl2detlog:' + k, v); } catch (e) { } } };
  let R = null; // last analysis
  let editedBack = null;

  // ---------- examples ----------
  const exSel = $('example');
  exSel.innerHTML = '<option value="">Examples…</option>' + P.EXAMPLES.map(e => '<option value="' + e.id + '">' + esc(e.title) + '</option>').join('');
  function loadExample(id) {
    const e = P.EXAMPLES.find(x => x.id === id); if (!e) return;
    $('src').value = e.src; $('queries').value = e.queries.join('\n'); $('sweep').value = e.sweep || ''; $('sweepvals').value = e.values || '';
    save();
  }
  exSel.onchange = () => { if (exSel.value) { loadExample(exSel.value); run(); } exSel.value = ''; };
  $('loadfile').onclick = () => $('file').click();
  $('file').onchange = async ev => { const f = ev.target.files[0]; if (!f) return; $('src').value = await f.text(); save(); setStatus('Opened ' + f.name + '. Add queries, then convert.'); };
  function save() { store.set('src', $('src').value); store.set('queries', $('queries').value); store.set('sweep', $('sweep').value); store.set('sweepvals', $('sweepvals').value); }
  ['src', 'queries', 'sweep', 'sweepvals'].forEach(id => $(id).addEventListener('input', save));
  if (store.get('src')) { $('src').value = store.get('src'); $('queries').value = store.get('queries') || ''; $('sweep').value = store.get('sweep') || ''; $('sweepvals').value = store.get('sweepvals') || ''; }
  else loadExample('fib');

  // tab key in editors
  for (const id of ['src', 'queries']) $(id).addEventListener('keydown', e => {
    if (e.key === 'Tab' && !e.shiftKey && !e.ctrlKey && !e.metaKey) { const t = e.target; const s = t.selectionStart; t.setRangeText('    ', s, t.selectionEnd, 'end'); e.preventDefault(); }
  });
  document.addEventListener('keydown', e => { if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') { e.preventDefault(); run(); } });

  // ---------- tabs ----------
  const tabs = [...document.querySelectorAll('.tab')];
  function showTab(name) { tabs.forEach(t => t.setAttribute('aria-selected', String(t.dataset.tab === name))); document.querySelectorAll('.pane').forEach(p => p.classList.toggle('on', p.id === 'p-' + name)); }
  tabs.forEach(t => t.onclick = () => showTab(t.dataset.tab));

  function setStatus(m, err) { const s = $('status'); s.textContent = m || ''; s.className = 'status' + (err ? ' err' : ''); }

  // ---------- run ----------
  function run() {
    save();
    const btn = $('convert'); btn.disabled = true; btn.textContent = 'Converting…';
    setStatus('Converting, running every query in Prolog and both Detlog forms, and checking the proof…');
    setTimeout(() => {
      try {
        const queries = $('queries').value.split('\n').map(s => s.trim()).filter(s => s && !s.startsWith('%'));
        const sweep = $('sweep').value.trim() ? { template: $('sweep').value.trim(), values: $('sweepvals').value.trim() || '1..10' } : null;
        const t0 = P.now();
        R = P.analyse($('src').value, queries, {
          mnn: { fuse: $('o-fuse').checked, splice: $('o-splice').checked, s2a: $('o-s2a').checked, memo: $('o-memo').checked },
          sweep, timing: $('o-time').checked
        });
        R.queries = queries; editedBack = null;
        if (R.errors.length && !R.plain) { setStatus(R.errors.join('\n'), true); renderError(R.errors.join('\n')); }
        else { renderAll(); setStatus('Done in ' + ((P.now() - t0) / 1000).toFixed(2) + ' s. ' + R.runs.length + ' queries' + (R.sweep ? ', sweep of ' + R.sweep.points.length + ' runs' : '') + '.'); }
      } catch (e) { console.error(e); setStatus(e.message, true); renderError(e.message); }
      btn.disabled = false; btn.textContent = 'Convert and prove';
    }, 30);
  }
  $('convert').onclick = run;
  function renderError(m) { $('p-stats').innerHTML = '<div class="errbox">' + esc(m) + '</div>'; showTab('stats'); }

  function renderAll() {
    renderStats(); renderDetlog('detlog', R.plain, 'Detlog'); renderDetlog('mnn', R.mnn, 'MNN-optimised Detlog');
    renderBack(); renderProof(); renderC(); renderExport();
  }

  // ---------- packets ----------
  function packetHtml(r) {
    if (!r) return '';
    if (r.error && !r.events.length) return '<div class="packet"><span class="chip err">' + esc(r.error) + '</span></div>';
    if (!r.events.length) return '<div class="packet"><span class="chip none">no answers</span></div>';
    const evs = r.events.slice(0, 14);
    let h = evs.map(e => e.k === 'out' ? '<span class="chip out" title="output">' + esc(JSON.stringify(e.text).slice(1, -1)) + '</span>' : '<span class="chip" title="answer">' + esc(e.text) + '</span>').join('');
    if (r.events.length > 14) h += '<span class="chip none">+' + (r.events.length - 14) + ' more</span>';
    if (r.error) h += '<span class="chip err">' + esc(r.error) + '</span>';
    return '<div class="packet">' + h + '</div>';
  }

  // ---------- stats ----------
  function renderStats() {
    const runs = R.runs; const same = runs.filter(r => r.same).length;
    const pl = sum(runs, r => r.prolog.steps), dl = sum(runs, r => r.plain.steps), mn = sum(runs, r => r.mnn.steps);
    const plt = sum(runs, r => r.prolog.ms), mnt = sum(runs, r => r.mnn.ms);
    const pf = R.proof;
    let h = '';
    if (R.errors.length) h += '<div class="errbox">' + esc(R.errors.join('\n')) + '</div>';
    const convErr = R.plain.errors.concat(R.mnn.errors.filter(e => !R.plain.errors.some(x => x.msg === e.msg)));
    if (convErr.length) h += '<div class="errbox">Not converted: ' + esc(convErr.map(e => e.msg).join('\n')) + '</div>';
    h += '<div class="verdict">' +
      '<div><b class="' + (same === runs.length ? 'good' : 'badc') + '">' + same + ' / ' + runs.length + '</b><span>queries with identical answer packets</span></div>' +
      '<div><b class="' + (pf.ok ? 'good' : 'badc') + '">' + (pf.ok ? 'Proved' : pf.fails + ' failed') + '</b><span>' + pf.checks.length + ' proof checks' + (pf.warns ? ', ' + pf.warns + ' with warnings' : '') + '</span></div>' +
      '<div>' + cmp(pl, mn, 'steps', fmt(pl) + ' vs ' + fmt(mn)) + '</div>' +
      '<div>' + (plt && mnt ? cmp(plt, mnt, 'time', ms(plt) + ' vs ' + ms(mnt) + ' ms') : '<b>—</b><span>time not measured</span>') + '</div></div>';
    h += '<h3>Answers and cost per query</h3><div class="scroll"><table><thead><tr><th>Query</th><th>Answer packet</th><th class="num">Prolog steps</th><th class="num">ms</th><th class="num">choice­points</th><th class="num">Detlog steps</th><th class="num">ms</th><th class="num">MNN steps</th><th class="num">ms</th><th class="num">decisions</th></tr></thead><tbody>';
    for (const r of runs) {
      h += '<tr><td class="q">' + esc(r.query) + ' ' + (r.same ? '<span class="badge ok">same</span>' : '<span class="badge bad">differs</span>') + '</td><td>' + packetHtml(r.prolog) +
        (r.same ? '' : '<div class="hint" style="margin-top:4px">Detlog:</div>' + packetHtml(r.plain) + '<div class="hint">MNN:</div>' + packetHtml(r.mnn)) + '</td>' +
        '<td class="num">' + fmt(r.prolog.steps) + '</td><td class="num">' + ms(r.prolog.ms) + '</td><td class="num">' + fmt(r.prolog.cps) + '</td>' +
        '<td class="num">' + fmt(r.plain.steps) + '</td><td class="num">' + ms(r.plain.ms) + '</td>' +
        '<td class="num">' + fmt(r.mnn.steps) + '</td><td class="num">' + ms(r.mnn.ms) + '</td><td class="num">' + fmt(r.mnn.decisions) + (r.mnn.memoHits ? '<div class="hint">' + fmt(r.mnn.memoHits) + ' memo hits</div>' : '') + '</td></tr>';
    }
    h += '</tbody></table></div>';
    h += '<p class="hint">A step is one goal call; Detlog also counts every packet item its runtime loops over. Prolog choicepoints are the alternatives it created; Detlog creates none — its decisions are if_commit/3 conditions, which never backtrack.' + (R.plain.report.length || R.mnn.report.length ? ' MNN S2A tables are computed at conversion time (' + ms(R.convertMnnMs) + ' ms in total).' : '') + '</p>';
    h += '<h3>Steps per query <span class="hint">(log scale)</span></h3>' + legend() + '<div class="chart" id="ch-steps"></div>';
    if (R.sweep) {
      const f = R.sweep.fit;
      h += '<h3>Complexity sweep: <span class="mono">' + esc(R.sweep.template) + '</span></h3>' + legend() +
        '<div class="chart" id="ch-sweep"></div>' +
        '<table style="margin-top:8px"><thead><tr><th>Fitted growth of steps in N</th><th>Prolog</th><th>Detlog</th><th>MNN Detlog</th></tr></thead><tbody><tr><td>class (exponent k)</td>' +
        [f.prolog, f.plain, f.mnn].map(x => '<td><b>' + esc(x.label) + '</b>' + (x.k != null && !x.exp ? ' <span class="hint">k = ' + x.k.toFixed(2) + '</span>' : '') + '</td>').join('') + '</tr></tbody></table>' +
        '<details><summary>Sweep data</summary><div class="scroll"><table><thead><tr><th class="num">N</th><th class="num">Prolog steps</th><th class="num">ms</th><th class="num">Detlog steps</th><th class="num">MNN steps</th><th class="num">ms</th><th>same</th></tr></thead><tbody>' +
        R.sweep.points.map(p => '<tr><td class="num">' + p.n + '</td><td class="num">' + fmt(p.prolog.steps) + '</td><td class="num">' + ms(p.prolog.ms) + '</td><td class="num">' + fmt(p.plain.steps) + '</td><td class="num">' + fmt(p.mnn.steps) + '</td><td class="num">' + ms(p.mnn.ms) + '</td><td>' + (p.same ? 'yes' : '<span class="badge bad">no</span>') + '</td></tr>').join('') + '</tbody></table></div></details>';
    }
    const m = R.metrics;
    const rows = [['Predicates', 'predicates'], ['Clauses', 'clauses'], ['Body goals', 'goals'], ['Longest body', 'maxBody'], ['Choicepoint sites', 'choiceSites'], ['Cuts', 'cuts'], ['if_commit decisions', 'decisions'], ['Auxiliary (packet loop) predicates', 'auxPredicates'], ['Cyclomatic complexity', 'cyclomatic'], ['Recursive predicates', 'recursive']];
    h += '<h3>Static complexity</h3><div class="scroll"><table><thead><tr><th>Measure</th><th class="num">Prolog</th><th class="num">Detlog</th><th class="num">MNN Detlog</th></tr></thead><tbody>' +
      rows.map(([l, k]) => '<tr><td>' + l + '</td><td class="num">' + val(m.prolog[k]) + '</td><td class="num">' + val(m.plain[k]) + '</td><td class="num">' + val(m.mnn[k]) + '</td></tr>').join('') + '</tbody></table></div>' +
      '<p class="hint">Choicepoint sites are multi-clause predicates, disjunctions and nondeterministic builtin calls. Detlog has none: every predicate has one clause or clauses told apart by their first argument. Its cyclomatic complexity counts if_commit branches and first-argument dispatch.</p>';
    $('p-stats').innerHTML = h;
    barChart($('ch-steps'), runs.map(r => ({ label: r.query, vals: [r.prolog.steps, r.plain.steps, r.mnn.steps] })));
    if (R.sweep) lineChart($('ch-sweep'), R.sweep.points.map(p => ({ x: p.n, vals: [p.prolog.error ? null : p.prolog.steps, p.plain.error ? null : p.plain.steps, p.mnn.error ? null : p.mnn.steps] })));
  }
  const val = v => v === undefined ? '—' : v;
  const sum = (a, f) => a.reduce((s, x) => s + (f(x) || 0), 0);
  // a: Prolog, b: MNN Detlog
  function cmp(a, b, what, detail) {
    if (!a || !b) return '<b>—</b><span>' + what + '</span>';
    const r = a / b, f = x => (x >= 10 ? x.toFixed(0) : x.toFixed(1)) + '×';
    return r >= 1 ? '<b class="good">' + f(r) + (what === 'time' ? ' faster' : ' fewer') + '</b><span>' + (what === 'time' ? 'MNN Detlog vs Prolog' : 'steps in MNN Detlog than Prolog') + ' (' + detail + ')</span>'
                  : '<b>' + f(1 / r) + (what === 'time' ? ' slower' : ' more') + '</b><span>' + (what === 'time' ? 'MNN Detlog vs Prolog' : 'steps in MNN Detlog than Prolog') + ' (' + detail + ')</span>';
  }
  function ratio(a, b) { if (!a || !b) return '—'; const r = a / b; return (r >= 10 ? r.toFixed(0) : r.toFixed(2)) + '×'; }
  const NAMES = ['Prolog', 'Detlog', 'MNN Detlog'];
  function legend() { return '<div class="legendrow">' + NAMES.map((n, i) => '<span><i style="background:var(--s' + (i + 1) + ')"></i>' + n + '</span>').join('') + '</div>'; }

  // ---------- charts (SVG, log scale, hover tooltips) ----------
  const tip = $('tip');
  function showTip(e, html) { tip.innerHTML = html; tip.style.display = 'block'; tip.style.left = e.pageX + 'px'; tip.style.top = e.pageY + 'px'; }
  function hideTip() { tip.style.display = 'none'; }
  function logTicks(max) { const t = []; for (let p = 1; p <= Math.max(10, max * 1.01); p *= 10) t.push(p); return t; }
  function barChart(el, data) {
    if (!el || !data.length) return;
    const W = 720, rowH = 30, padL = 170, padR = 16, padT = 22, H = padT + data.length * rowH + 8;
    const max = Math.max(10, ...data.flatMap(d => d.vals.filter(Boolean)));
    const lmax = Math.log10(max * 1.2);
    const x = v => padL + (W - padL - padR) * (Math.log10(Math.max(1, v)) / lmax);
    let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="Steps per query, log scale">';
    for (const t of logTicks(max)) { const xx = x(t); s += '<line class="gl" x1="' + xx + '" x2="' + xx + '" y1="' + (padT - 6) + '" y2="' + (H - 4) + '"/><text class="ax" x="' + xx + '" y="' + (padT - 10) + '" text-anchor="middle">' + fmt(t) + '</text>'; }
    data.forEach((d, i) => {
      const y0 = padT + i * rowH;
      const lbl = d.label.length > 24 ? d.label.slice(0, 23) + '…' : d.label;
      s += '<text class="lab" x="' + (padL - 8) + '" y="' + (y0 + 16) + '" text-anchor="end">' + esc(lbl) + '</text>';
      d.vals.forEach((v, j) => {
        if (!v) return;
        const y = y0 + 3 + j * 8; const w = Math.max(2, x(v) - padL);
        s += '<rect x="' + padL + '" y="' + y + '" width="' + w + '" height="6" rx="2" fill="var(--s' + (j + 1) + ')" data-i="' + i + '"/>';
      });
      s += '<rect x="0" y="' + y0 + '" width="' + W + '" height="' + rowH + '" fill="transparent" data-i="' + i + '" class="hit"/>';
    });
    s += '</svg>';
    el.innerHTML = s;
    el.querySelectorAll('.hit').forEach(r => { r.addEventListener('mousemove', e => { const d = data[+r.dataset.i]; showTip(e, '<b>' + esc(d.label) + '</b><br>' + NAMES.map((n, j) => n + ': ' + fmt(d.vals[j]) + ' steps').join('<br>')); }); r.addEventListener('mouseleave', hideTip); });
  }
  function lineChart(el, pts) {
    if (!el || pts.length < 2) return;
    const W = 720, H = 280, padL = 56, padR = 96, padT = 14, padB = 30;
    const xs = pts.map(p => p.x); const xmin = Math.min(...xs), xmax = Math.max(...xs);
    const max = Math.max(10, ...pts.flatMap(p => p.vals.filter(Boolean)));
    const lmax = Math.log10(max * 1.3);
    const X = v => padL + (W - padL - padR) * ((v - xmin) / Math.max(1, xmax - xmin));
    const Y = v => padT + (H - padT - padB) * (1 - Math.log10(Math.max(1, v)) / lmax);
    let s = '<svg viewBox="0 0 ' + W + ' ' + H + '" role="img" aria-label="Steps against N, log scale">';
    for (const t of logTicks(max)) { const yy = Y(t); s += '<line class="gl" x1="' + padL + '" x2="' + (W - padR) + '" y1="' + yy + '" y2="' + yy + '"/><text class="ax" x="' + (padL - 6) + '" y="' + (yy + 4) + '" text-anchor="end">' + fmt(t) + '</text>'; }
    for (const p of pts) s += '<text class="ax" x="' + X(p.x) + '" y="' + (H - 10) + '" text-anchor="middle">' + p.x + '</text>';
    for (let j = 0; j < 3; j++) {
      const ok = pts.filter(p => p.vals[j]);
      if (!ok.length) continue;
      s += '<polyline fill="none" stroke="var(--s' + (j + 1) + ')" stroke-width="2" stroke-linejoin="round" points="' + ok.map(p => X(p.x) + ',' + Y(p.vals[j])).join(' ') + '"/>';
      for (const p of ok) s += '<circle cx="' + X(p.x) + '" cy="' + Y(p.vals[j]) + '" r="4" fill="var(--s' + (j + 1) + ')" stroke="var(--sheet)" stroke-width="2"/>';
      const lp = ok[ok.length - 1];
      s += '<text class="lab" x="' + (X(lp.x) + 8) + '" y="' + (Y(lp.vals[j]) + 4 + (j - 1) * 2) + '">' + NAMES[j] + '</text>';
    }
    const cw = (W - padL - padR) / Math.max(1, pts.length - 1);
    pts.forEach((p, i) => { s += '<rect class="hit" data-i="' + i + '" x="' + (X(p.x) - cw / 2) + '" y="' + padT + '" width="' + cw + '" height="' + (H - padT - padB) + '" fill="transparent"/>'; });
    s += '<line id="xh" class="gl" y1="' + padT + '" y2="' + (H - padB) + '" x1="-10" x2="-10" style="stroke:var(--ink-3);display:none"/></svg>';
    el.innerHTML = s;
    const xh = el.querySelector('#xh');
    el.querySelectorAll('.hit').forEach(r => { r.addEventListener('mousemove', e => { const p = pts[+r.dataset.i]; xh.style.display = ''; xh.setAttribute('x1', X(p.x)); xh.setAttribute('x2', X(p.x)); showTip(e, '<b>N = ' + p.x + '</b><br>' + NAMES.map((n, j) => n + ': ' + fmt(p.vals[j]) + ' steps').join('<br>')); }); r.addEventListener('mouseleave', () => { hideTip(); xh.style.display = 'none'; }); });
  }

  // ---------- Detlog views (editable) ----------
  function renderDetlog(id, conv, label) {
    const pane = $('p-' + id);
    let h = '<div class="row-actions"><button class="btn" data-act="back">Back-convert this Detlog to Prolog</button><button class="btn" data-act="reset">Restore generated</button><span class="hint">Edit the Detlog, then back-convert: changes are reported against your source.</span></div>';
    if (conv.errors.length) h += '<div class="errbox">' + esc(conv.errors.map(e => e.msg).join('\n')) + '</div>';
    const notes = conv.genPreds.filter(g => g.notes.length || g.kind === 'memo' || g.kind === 's2a');
    if (id === 'mnn' && notes.length) h += '<details open><summary>What MNN optimisation did</summary><ul>' + notes.map(g => '<li><code>' + esc(g.key) + '</code>: ' + esc(g.notes.join('; ')) + '</li>').join('') + '</ul></details>';
    if (conv.warnings.length) h += '<details><summary>' + conv.warnings.length + ' conversion note(s)</summary><ul>' + conv.warnings.map(w => '<li>' + (w.pred ? '<code>' + esc(w.pred) + '</code>: ' : '') + esc(w.msg) + '</li>').join('') + '</ul></details>';
    h += '<label class="sr" for="ta-' + id + '">' + label + '</label><textarea id="ta-' + id + '" class="code dl" spellcheck="false"></textarea>';
    pane.innerHTML = h;
    const ta = $('ta-' + id); ta.value = exportDetlogText(conv, false);
    pane.querySelector('[data-act=back]').onclick = () => { backFromText(ta.value, label); };
    pane.querySelector('[data-act=reset]').onclick = () => { ta.value = exportDetlogText(conv, false); };
  }
  // Detlog text without the sweep queries
  function exportDetlogText(conv, withRuntime) {
    const n = R.queries.length;
    const keepQ = new Set(conv.queries.slice(0, n).map(q => q.key));
    const drop = new Set(conv.queries.slice(n).map(q => q.key));
    const clauses = conv.clauses.filter(c => !drop.has(c.pred));
    let text = P.printDetlog(Object.assign({}, conv, { clauses }));
    if (n) text += '\n% Queries: ' + conv.queries.slice(0, n).map(q => q.pred + '__cp/' + (q.vars.length + 1) + ' is ?- ' + q.text).join('; ') + '\n';
    if (withRuntime) {
      const rt = document.getElementById('pl2d-rt-pl').textContent;
      text = ':- style_check(-singleton).\n' + rt + '\n% ================= converted program =================\n' + text +
        '\n% Run all queries:  ?- detlog_run_all.\n' + 'detlog_run_all :- ' + (n ? conv.queries.slice(0, n).map((q, i) => 'detlog_run_q' + (i + 1)).join(', ') : 'true') + '.\n' +
        conv.queries.slice(0, n).map((q, i) => 'detlog_run_q' + (i + 1) + ' :- format("?- ~w.~n", [' + P.show(P.Str(q.text)) + "]), '" + q.pred + "__cp'(" + q.vars.concat(['R__']).join(', ') + '), detlog_print([' + q.vars.map(v => "'" + v + "'").join(', ') + '], R__).\n').join('');
    }
    return text;
  }

  // ---------- back-conversion ----------
  function backFromText(text, label) {
    try {
      const b = P.backConvert(text);
      const cw = P.changeWarnings($('src').value, b.text, b);
      // re-check by evaluation
      const evals = R.queries.map(q => { const ref = R.runs.find(r => r.query === q.replace(/\.\s*$/, '')); let back; try { back = P.runQuery(b.text, q, { stepLimit: 3e6 }); } catch (e) { back = { events: [], error: e.message }; } return { q, same: ref && JSON.stringify(ref.prolog.events) === JSON.stringify(back.events), back }; });
      editedBack = { b, cw, evals, label };
      renderBack(); showTab('back');
    } catch (e) { setStatus('Back-conversion failed: ' + e.message, true); }
  }
  function renderBack() {
    let b, cw, evals, label;
    if (editedBack) ({ b, cw, evals, label } = editedBack);
    else { b = R.backPlain; cw = R.changes; label = 'Detlog'; evals = R.runs.map(r => ({ q: r.query, same: r.back && JSON.stringify(r.back.events) === JSON.stringify(r.prolog.events), back: r.back })); }
    const pane = $('p-back');
    if (!b) { pane.innerHTML = '<div class="errbox">Back-conversion failed.</div>'; return; }
    const changed = cw.filter(w => w.kind !== 'same'), bad = cw.filter(w => w.kind === 'error' || w.kind === 'removed');
    const evOk = evals.every(e => e.same);
    const badge = $('b-back'); badge.textContent = changed.length ? changed.length + ' change' + (changed.length > 1 ? 's' : '') : 'exact'; badge.className = 'badge ' + (bad.length || !evOk ? 'bad' : changed.length ? 'warn' : 'ok');
    let h = '<div class="row-actions">';
    if (!editedBack) h += '<label>From <select id="backsrc"><option value="plain">Detlog</option><option value="mnn">MNN Detlog</option></select></label>';
    else h += '<span>From your edited ' + esc(label) + '.</span> <button class="btn" id="backgen">Show the generated Detlog\'s back-conversion</button>';
    h += '<button class="btn" id="dlback">Download .pl</button></div>';
    h += '<h3>Change warnings</h3>';
    if (!changed.length) h += '<p>Every predicate came back exactly as written in your source.</p>';
    else h += '<ul class="warnlist">' + changed.map(w => '<li class="' + w.kind + '"><code>' + esc(w.pred) + '</code> — ' + esc(w.msg) + (w.notes && w.notes.length ? '<div class="hint">' + esc(w.notes.join('; ')) + '</div>' : '') + (w.diff ? '<div class="diff">' + w.diff.slice(0, 8).map(d => (d.was ? '<div class="was">' + esc(d.was) + '</div>' : '') + (d.now ? '<div class="now">' + esc(d.now) + '</div>' : '')).join('') + (w.diff.length > 8 ? '<div class="hint">… ' + (w.diff.length - 8) + ' more</div>' : '') + '</div>' : '') + '</li>').join('') + '</ul>';
    h += '<p class="hint">' + cw.filter(w => w.kind === 'same').length + ' predicate(s) unchanged. Changes are equivalent rewrites unless an evaluation below differs.</p>';
    h += '<h3>Proof by evaluation</h3><table><thead><tr><th>Query</th><th>Back-converted Prolog vs source</th></tr></thead><tbody>' + evals.map(e => '<tr><td class="q">' + esc(e.q) + '</td><td>' + (e.same ? '<span class="badge ok">same packet</span>' : '<span class="badge bad">differs</span>' + packetHtml(e.back)) + '</td></tr>').join('') + '</tbody></table>';
    h += '<h3>Prolog</h3><pre class="out" id="backtext"></pre>';
    pane.innerHTML = h;
    $('backtext').textContent = backText(b, cw);
    $('dlback').onclick = () => download('program_back.pl', backText(b, cw));
    if ($('backsrc')) { $('backsrc').value = renderBack.src || 'plain'; $('backsrc').onchange = e => { renderBack.src = e.target.value; const isM = e.target.value === 'mnn'; editedBack = { b: isM ? R.backMnn : R.backPlain, cw: isM ? R.changesMnn : R.changes, evals: R.runs.map(r => ({ q: r.query, same: (isM ? r.backMnn : r.back) && JSON.stringify((isM ? r.backMnn : r.back).events) === JSON.stringify(r.prolog.events), back: isM ? r.backMnn : r.back })), label: isM ? 'MNN Detlog' : 'Detlog', generated: true }; renderBack(); }; }
    if (editedBack && editedBack.generated) { const bs = pane.querySelector('#backgen'); if (bs) bs.remove(); pane.querySelector('.row-actions span').textContent = 'From the generated ' + label + '.'; }
    if ($('backgen')) $('backgen').onclick = () => { editedBack = null; renderBack(); };
  }
  function backText(b, cw) {
    const changed = cw.filter(w => w.kind !== 'same');
    let head = '% Back-converted from Detlog by pl2detlog.\n';
    if (changed.length) head += '% Change warnings (against the original source):\n' + changed.map(w => '%   ' + w.pred + ': ' + w.msg).join('\n') + '\n';
    else head += '% No changes: every predicate is as written in the source.\n';
    return head + b.text.replace(/^% Prolog back-converted from Detlog by pl2detlog\.\n/, '');
  }

  // ---------- proof ----------
  function renderProof() {
    const pf = R.proof; const b = $('b-proof');
    b.textContent = pf.ok ? (pf.warns ? pf.warns + ' warn' : 'ok') : pf.fails + ' failed'; b.className = 'badge ' + (pf.ok ? (pf.warns ? 'warn' : 'ok') : 'bad');
    let h = '<div class="row-actions"><button class="btn" id="dlproof">Download proof report</button><span class="hint">The checker is independent of the converter: it re-derives each side condition and re-runs every query.</span></div>';
    let g = null;
    for (const c of pf.checks) {
      if (c.group !== g) { if (g) h += '</ul>'; h += '<h3>' + esc(c.group) + '</h3><ul class="checks">'; g = c.group; }
      h += '<li><span>' + (c.ok === true ? '<span class="badge ok">ok</span>' : c.ok === 'warn' ? '<span class="badge warn">warn</span>' : '<span class="badge bad">fail</span>') + '</span><div>' + esc(c.name) + (c.detail ? '<div class="d">' + esc(c.detail) + '</div>' : '') + '</div></li>';
    }
    if (g) h += '</ul>';
    h += '<details><summary>Proof steps of the MNN Detlog (' + R.mnn.steps.length + ')</summary>' + stepsTable(R.mnn) + '</details>';
    h += '<details><summary>Proof steps of the plain Detlog (' + R.plain.steps.length + ')</summary>' + stepsTable(R.plain) + '</details>';
    h += '<details><summary>Rules</summary><table><tbody>' + P.RULE_DOC.map(([r, d]) => '<tr><td><code>' + r + '</code></td><td>' + esc(d) + '</td></tr>').join('') + '</tbody></table></details>';
    $('p-proof').innerHTML = h;
    $('dlproof').onclick = () => download('proof.txt', pf.text);
  }
  function stepsTable(conv) {
    const steps = conv.steps.filter(s => !/^\$query/.test(s.pred) || conv.queries.slice(0, R.queries.length).some(q => q.key === s.pred));
    return '<div class="scroll"><table><thead><tr><th class="num">#</th><th>Rule</th><th>Predicate</th><th>Source</th><th>Clauses</th></tr></thead><tbody>' +
      steps.slice(0, 600).map(s => '<tr><td class="num">' + s.id + '</td><td><code>' + s.rule + '</code></td><td><code>' + esc(s.pred) + '</code></td><td class="mono" style="white-space:pre-wrap">' + esc(String(s.src).slice(0, 220)) + (s.info && s.info.formula ? '<div class="hint">' + esc(s.info.formula) + '</div>' : '') + '</td><td class="num">' + (s.clauses.length ? s.clauses.map(i => i + 1).join(', ') : '') + '</td></tr>').join('') + '</tbody></table></div>';
  }

  // ---------- C ----------
  function cFor(conv) { return P.toC(exportDetlogText(conv, false), { queries: conv.queries.slice(0, R.queries.length), mode: conv.mode === 'mnn' ? 'MNN-optimised Detlog' : 'Detlog' }); }
  function renderC() {
    const which = renderC.which || 'mnn';
    const conv = which === 'mnn' ? R.mnn : R.plain;
    let c; try { c = cFor(conv); } catch (e) { $('p-c').innerHTML = '<div class="errbox">' + esc(e.message) + '</div>'; return; }
    let h = '<div class="row-actions"><label>From <select id="csrc"><option value="mnn">MNN Detlog</option><option value="plain">Detlog</option></select></label><button class="btn" id="dlc">Download .c</button><span class="hint">Build with <code>cc -O2 -o prog prog.c -lm</code>, run <code>./prog</code>, time with <code>./prog -r 1000</code>.</span></div>';
    if (c.warnings.length) h += '<div class="errbox">' + esc(c.warnings.join('\n')) + '</div>';
    h += '<p class="hint">One C function per Detlog predicate selects its clause by the first argument and commits to it; if_commit/3 is a trail mark, the condition, and an undo before the else branch. There is no choicepoint stack.</p><pre class="out" id="ctext"></pre>';
    $('p-c').innerHTML = h;
    $('ctext').textContent = c.code.length > 400000 ? c.code.slice(0, 400000) + '\n/* … truncated in view; download for the full file */' : c.code;
    $('csrc').value = which; $('csrc').onchange = e => { renderC.which = e.target.value; renderC(); };
    $('dlc').onclick = () => download(which === 'mnn' ? 'program_mnn.c' : 'program.c', c.code);
  }

  // ---------- export ----------
  function renderExport() {
    const items = [
      ['html', 'HTML page', 'A self-contained page that runs the MNN Detlog queries in the browser and shows their answers and steps.'],
      ['detlog', 'Detlog (.pl)', 'The MNN-optimised Detlog with the Detlog runtime included: consult it in SWI-Prolog and run ?- detlog_run_all.'],
      ['detlog-plain', 'Plain Detlog (.pl)', 'The unoptimised Detlog, also with the runtime.'],
      ['c', 'C (.c)', 'The MNN Detlog compiled to C with its runtime.'],
      ['prolog', 'Prolog, back-converted (.pl)', 'Detlog turned back into Prolog, with change warnings as comments.'],
      ['proof', 'Proof report (.txt)', 'Every check, every rewrite step and the rules.'],
      ['runtime', 'Detlog runtime (.pl)', 'detlog_runtime.pl on its own.']
    ];
    $('p-export').innerHTML = '<table><tbody>' + items.map(([k, t, d]) => '<tr><td style="width:220px"><button class="btn" data-ex="' + k + '">' + esc(t) + '</button></td><td class="hint">' + esc(d) + '</td></tr>').join('') + '</tbody></table>';
    $('p-export').querySelectorAll('[data-ex]').forEach(b => b.onclick = () => doExport(b.dataset.ex));
  }
  function doExport(k) {
    if (!R) return;
    switch (k) {
      case 'html': return download('program_detlog.html', htmlExport());
      case 'detlog': return download('program_mnn_detlog.pl', exportDetlogText(R.mnn, true));
      case 'detlog-plain': return download('program_detlog.pl', exportDetlogText(R.plain, true));
      case 'c': return download('program_mnn.c', cFor(R.mnn).code);
      case 'prolog': return download('program_back.pl', backText(R.backPlain, R.changes));
      case 'proof': return download('proof.txt', R.proof.text);
      case 'runtime': return download('detlog_runtime.pl', document.getElementById('pl2d-rt-pl').textContent);
    }
  }
  function htmlExport() {
    const lib = document.getElementById('pl2d-lib').textContent;
    const det = exportDetlogText(R.mnn, false);
    const qs = R.mnn.queries.slice(0, R.queries.length).filter(q => !q.error);
    const data = JSON.stringify({ detlog: det, queries: qs.map(q => ({ text: q.text, pred: q.pred, vars: q.vars })) }).replace(/</g, '\\u003c');
    const S = 'script';
    return '<!DOCTYPE html>\n<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><title>Detlog program</title>' +
      '<style>body{font:15px/1.5 -apple-system,"Segoe UI",system-ui,sans-serif;margin:0;padding:28px;max-width:960px;color:#172033;background:#eef1f4}h1{font:600 24px Georgia,serif;margin:0 0 4px}pre{background:#fff;border:1px solid #d3d9e1;border-radius:8px;padding:12px;overflow:auto;font:12.5px/1.5 ui-monospace,Menlo,monospace;max-height:60vh}table{border-collapse:collapse;width:100%;background:#fff;border:1px solid #d3d9e1;border-radius:8px}td,th{padding:7px 10px;border-bottom:1px solid #e4e8ee;text-align:left;vertical-align:top}code{font:12.5px ui-monospace,Menlo,monospace}.n{text-align:right;font-variant-numeric:tabular-nums}button{font:inherit;padding:6px 14px;border-radius:6px;border:1px solid #3446c4;background:#3446c4;color:#fff;cursor:pointer}</style></head><body>' +
      '<h1>Detlog program</h1><p>Generated by pl2detlog. The queries run without choicepoints: every call commits to the clause its first argument selects.</p>' +
      '<p><button id="run">Run again</button></p><table><thead><tr><th>Query</th><th>Answers and output</th><th class="n">Steps</th><th class="n">ms</th></tr></thead><tbody id="res"></tbody></table>' +
      '<h2 style="font:600 18px Georgia,serif">Detlog</h2><pre id="code"></pre>' +
      '<' + S + '>' + lib + '</' + S + '>' +
      '<' + S + '>(function(){var D=' + data + ';var P=window.PL2D;document.getElementById("code").textContent=D.detlog;var prog=P.loadProgram(D.detlog);' +
      'function esc(s){return String(s).replace(/[&<>]/g,function(c){return{"&":"&amp;","<":"&lt;",">":"&gt;"}[c]})}' +
      'function run(){var h="";D.queries.forEach(function(q){var r=P.runDetlog(prog,q.pred,q.vars,{});var a=r.events.map(function(e){return e.k==="out"?"<code style=\\"color:#7a3b06\\">"+esc(e.text)+"</code>":"<code>"+esc(e.text)+"</code>"}).join("<br>")||(r.error?"<b>"+esc(r.error)+"</b>":"no answers");h+="<tr><td><code>?- "+esc(q.text)+"</code></td><td>"+a+"</td><td class=n>"+r.steps+"</td><td class=n>"+r.timeMs.toFixed(3)+"</td></tr>"});document.getElementById("res").innerHTML=h}' +
      'document.getElementById("run").onclick=run;run();})();</' + S + '></body></html>\n';
  }
  function download(name, text) {
    const a = document.createElement('a'); a.href = URL.createObjectURL(new Blob([text], { type: 'text/plain;charset=utf-8' })); a.download = name; document.body.appendChild(a); a.click();
    setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500);
    setStatus('Downloaded ' + name + '.');
  }

  window.PL2D_APP = { htmlExport, exportDetlogText, cFor, backText, get result() { return R; }, run };
  run();
})();
