/* swi.js - SWI-Prolog compatibility for the reference engine, so that ordinary SWI-Prolog programs
   (LucianOS's among them) run unchanged on the interpreter (src/interp.js):

   - dicts (read by core.js as dict(Tag, [K-V, ...])): is_dict, get_dict, put_dict, del_dict,
     dict_pairs, dict_create
   - JSON as library(http/json) reads and writes it: atom_json_dict, atom_json_term, json_read_dict,
     json_write_dict, json_write, json_read
   - streams and files through the engine's io: open, close, read_line_to_string/codes, read_term,
     read, read_string, write/2, format/3 to streams, user_input/user_output/user_error,
     read_file_to_string, read_file_to_terms, exists_file, absolute_file_name, ...
   - modules: module/2 and use_module/1,2 directives are read (library modules are built in, file
     modules are loaded by the interpreter); Module:Goal calls Goal
   - clause/2, current_prolog_flag/2 (argv), print_message/2, setup_call_cleanup/3 and a few more

   The engine's io object answers for the file system and the process; the interpreter makes it. */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, list, deref: D, listToArray, copy, show, compare, isGround } = P;
  const B = P.builtins;
  const det = (k, fn) => { B[k] = { fn }; };
  const nondet = (k, fn) => { B[k] = { fn, nondet: true }; };
  const callb = (k, fn) => { B[k] = { fn, call: true }; };
  const err = (formal) => new P.PlError(Cmp('error', [formal, Var()]));
  const domErr = (d, c) => err(Cmp('domain_error', [Atom(d), c]));
  const existErr = (k, c) => err(Cmp('existence_error', [Atom(k), c]));
  const permErr = (a, t, c) => err(Cmp('permission_error', [Atom(a), Atom(t), c]));
  const textOf = (t) => P.textOf(t);
  const SWI = (t, quoted) => show(t, { quoted, swi: !!P.SWI_WRITE });

  // ---------------------------------------------------------------- dicts
  const isDict = (t) => P.dictPairs(t) !== null;
  const dictOf = (t) => { const ps = P.dictPairs(t); if (!ps) { if (D(t).t === 'v') throw P.instErr(); throw P.typeError('dict', t); } return ps; };
  const mk = (tag, ps) => P.mkDict(tag, ps);
  det('is_dict/1', (a) => isDict(a[0]));
  det('is_dict/2', (a, e) => isDict(a[0]) && e.unify(a[1], D(a[0]).a[0]));
  nondet('get_dict/3', function* (a, e) {
    const ps = dictOf(a[1]), k = D(a[0]);
    if (k.t !== 'v') { const p = ps.find(([kk]) => compare(kk, k) === 0); if (p && e.unify(a[2], p[1])) yield 'last'; return; }
    for (const [kk, v] of ps) { const m = e.mark(); if (e.unify(k, kk) && e.unify(a[2], v)) yield; e.undo(m); }
  });
  det('put_dict/4', (a, e) => { const ps = dictOf(a[1]).filter(([k]) => compare(k, D(a[0])) !== 0); ps.push([D(a[0]), a[2]]); return e.unify(a[3], mk(D(a[1]).a[0], ps)); });
  det('put_dict/3', (a, e) => {
    const nw = isDict(a[0]) ? dictOf(a[0]) : (listToArray(a[0]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; });
    const ps = dictOf(a[1]).filter(([k]) => !nw.some(([k2]) => compare(k, k2) === 0)).concat(nw);
    return e.unify(a[2], mk(D(a[1]).a[0], ps));
  });
  det('del_dict/4', (a, e) => { const ps = dictOf(a[1]); const i = ps.findIndex(([k]) => compare(k, D(a[0])) === 0); if (i < 0 || !e.unify(a[2], ps[i][1])) return false; ps.splice(i, 1); return e.unify(a[3], mk(D(a[1]).a[0], ps)); });
  det('dict_pairs/3', (a, e) => {
    const d = D(a[0]);
    if (d.t !== 'v') { const ps = dictOf(d); return e.unify(a[1], d.a[0]) && e.unify(a[2], list(ps.map(([k, v]) => Cmp('-', [k, v])))); }
    const ps = (listToArray(a[2]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; });
    return e.unify(d, mk(a[1], ps));
  });
  det('dict_create/3', (a, e) => { const ps = (listToArray(a[2]) || []).map((x) => { x = D(x); return [D(x.a[0]), x.a[1]]; }); return e.unify(a[0], mk(a[1], ps)); });
  det('get_dict/5', (a, e) => { const ps = dictOf(a[1]); const i = ps.findIndex(([k]) => compare(k, D(a[0])) === 0); if (i < 0 || !e.unify(a[2], ps[i][1])) return false; ps[i] = [ps[i][0], a[3]]; return e.unify(a[4], mk(D(a[1]).a[0], ps)); });

  // ---------------------------------------------------------------- JSON
  // value_string_as: strings by default (as SWI-Prolog's atom_json_dict); true/false/null as atoms
  function parseJSON(text, dicts, opts = {}) {
    let v; try { v = JSON.parse(text); } catch (x) { throw err(Cmp('syntax_error', [Atom('json(' + x.message.replace(/[^a-z0-9 ]/gi, '').slice(0, 60) + ')')])); }
    const strAs = opts.strAs || (dicts ? 'string' : 'atom');
    const tr = (x) => {
      if (x === null) return Atom('null'); if (x === true) return Atom('true'); if (x === false) return Atom('false');
      if (typeof x === 'number') return Number.isInteger(x) ? Int(x) : Num(x, true);
      if (typeof x === 'string') return strAs === 'atom' ? Atom(x) : Str(x);
      if (Array.isArray(x)) return list(x.map(tr));
      if (dicts) return mk(opts.tag || Var(), Object.keys(x).map((k) => [/^-?\d+$/.test(k) && Number.isSafeInteger(+k) ? Int(+k) : Atom(k), tr(x[k])]));
      return Cmp('json', [list(Object.keys(x).map((k) => Cmp('=', [Atom(k), tr(x[k])])))]);
    };
    return tr(v);
  }
  function toJSONValue(t) {
    t = D(t);
    switch (t.t) {
      case 'v': throw P.instErr();
      case 'n': return typeof t.v === 'bigint' ? { raw: t.v.toString() } : t.v;
      case 's': return t.v;
      case 'a': return t.n === 'null' ? null : t.n === 'true' ? true : t.n === 'false' ? false : t.n === '[]' ? [] : t.n;
      case 'c': {
        if (t.f === 'dict' && isDict(t)) { const o = {}; for (const [k, v] of P.dictPairs(t)) o[textOf(k)] = toJSONValue(v); return o; }
        if (t.f === 'json' && t.a.length === 1) { const o = {}; for (const x of listToArray(t.a[0]) || []) { const p = D(x); o[textOf(p.a[0])] = toJSONValue(p.a[1]); } return o; }
        if (t.f === '.' && t.a.length === 2) { const l = listToArray(t); if (l) return l.map(toJSONValue); }
        if (t.f === '@' && t.a.length === 1) return toJSONValue(t.a[0]);
        if (t.f === 'string' && t.a.length === 1) return textOf(t.a[0]);
        throw P.typeError('json_term', t);
      }
    }
  }
  // as SWI-Prolog writes JSON: width(0) on one line ({"a":1, "b":2}), otherwise laid out with 2 spaces
  function writeJSON(v, pretty, ind = 0) {
    const q = (s) => JSON.stringify(s);
    if (v && typeof v === 'object' && 'raw' in v && Object.keys(v).length === 1) return v.raw;
    if (Array.isArray(v)) {
      if (!v.length) return '[]';
      if (!pretty) return '[' + v.map((x) => writeJSON(x, false)).join(', ') + ']';
      const simple = v.every((x) => x === null || typeof x !== 'object');
      if (simple) { const one = '[' + v.map((x) => writeJSON(x, false)).join(', ') + ']'; if (one.length + ind < 72) return one; }
      return '[\n' + v.map((x) => ' '.repeat(ind + 2) + writeJSON(x, true, ind + 2)).join(',\n') + '\n' + ' '.repeat(ind) + ']';
    }
    if (v && typeof v === 'object') {
      const ks = Object.keys(v); if (!ks.length) return '{}';
      if (!pretty) return '{' + ks.map((k) => q(k) + ':' + writeJSON(v[k], false)).join(', ') + '}';
      const one = '{' + ks.map((k) => q(k) + ':' + writeJSON(v[k], false)).join(', ') + '}';
      if (one.length + ind < 72 && !one.includes('{', 1)) return one;
      return '{\n' + ks.map((k) => ' '.repeat(ind + 2) + q(k) + ':' + writeJSON(v[k], true, ind + 2)).join(',\n') + '\n' + ' '.repeat(ind) + '}';
    }
    if (typeof v === 'number') return Number.isInteger(v) ? String(v) : String(v).includes('e') || String(v).includes('.') ? String(v) : String(v) + '.0';
    return q(v);
  }
  const jsonOpts = (o) => { const r = { pretty: true, strAs: null, tag: null }; for (const x of listToArray(o) || []) { const t = D(x); if (t.t === 'c' && t.a.length === 1) { const v = D(t.a[0]); if (t.f === 'width' && v.t === 'n' && v.v === 0) r.pretty = false; if (t.f === 'value_string_as') r.strAs = v.n; if (t.f === 'tag') r.tag = v; } } return r; };
  det('atom_json_dict/3', (a, e) => {
    const t = D(a[0]), o = jsonOpts(a[2]);
    if (t.t !== 'v') return e.unify(a[1], parseJSON(textOf(t), true, o));
    return e.unify(t, Atom(writeJSON(toJSONValue(a[1]), o.pretty)));
  });
  det('atom_json_term/3', (a, e) => {
    const t = D(a[0]), o = jsonOpts(a[2]);
    if (t.t !== 'v') return e.unify(a[1], parseJSON(textOf(t), false, o));
    return e.unify(t, Atom(writeJSON(toJSONValue(a[1]), o.pretty)));
  });
  det('json_read_dict/2', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), true)));
  det('json_read_dict/3', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), true, jsonOpts(a[2]))));
  det('json_read/2', (a, e) => e.unify(a[1], parseJSON(readAll(e, a[0]), false)));
  det('json_write_dict/2', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), true)); return true; });
  det('json_write_dict/3', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), jsonOpts(a[2]).pretty)); return true; });
  det('json_write/2', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), true)); return true; });
  det('json_write/3', (a, e) => { put(e, a[0], writeJSON(toJSONValue(a[1]), jsonOpts(a[2]).pretty)); return true; });

  // ---------------------------------------------------------------- files and streams
  const io = (e) => e.io || P.defaultIO || null;
  // an io call that fails (no such file, no permission) raises the Prolog error SWI-Prolog would
  const ioDo = (what, path, f) => { try { return f(); } catch (x) { if (x instanceof P.PlError) throw x; if (x && x.code === 'ENOENT') throw existErr('file', Atom(path)); throw permErr(what, 'file', Atom(path)); } };
  const resolvePath = (e, p) => { const cwd = (io(e) && io(e).cwd) || ''; return P.joinPath(cwd, p); };
  P.joinPath = (cwd, p) => {
    if (!p) return cwd || '.';
    if (/^([A-Za-z]:)?[\\/]/.test(p) || !cwd || cwd === '.') return normal(p);
    return normal(cwd.replace(/[\\/]+$/, '') + '/' + p);
  };
  function normal(p) { const abs = p.startsWith('/'); const out = []; for (const s of p.split(/[\\/]+/)) { if (!s || s === '.') continue; if (s === '..' && out.length && out[out.length - 1] !== '..') out.pop(); else out.push(s); } const r = (abs ? '/' : '') + out.join('/'); return r || (abs ? '/' : '.'); }
  const fileText = (e, path) => { const x = io(e); const t = x && x.readFile ? x.readFile(path) : null; if (t == null) throw existErr('source_sink', Atom(path)); return t; };
  function streamOf(e, t, mode) {
    t = D(t);
    if (t.t === 'v') throw P.instErr();
    if (t.t === 'a') {
      if (t.n === 'user_output' || t.n === 'current_output') return { id: 'out', mode: 'write' };
      if (t.n === 'user_error') return { id: 'err', mode: 'write' };
      if (t.n === 'user_input' || t.n === 'current_input') {
        // standard input is read as it is needed (io.readStdin() gives the next piece, or null at its end)
        if (!e.streams.has('in')) { const x = io(e) || {}; e.streams.set('in', { id: 'in', mode: 'read', text: typeof x.stdin === 'string' ? x.stdin : '', pos: 0, line: 1, more: x.readStdin ? () => x.readStdin() : null }); }
        return e.streams.get('in');
      }
      for (const s of e.streams.values()) if (s.alias === t.n) return s;
    }
    if (t.t === 'c' && t.f === '$stream' && t.a.length === 1) { const s = e.streams.get(D(t.a[0]).v); if (s) return s; }
    throw existErr('stream', t);
  }
  function put(e, st, text) {
    const s = st && st.mode ? st : streamOf(e, st);
    if (s.mode !== 'write' && s.mode !== 'append') throw permErr('output', 'stream', Atom(String(s.id)));
    if (s.id === 'out') e.write(text); else if (s.id === 'err') e.writeErr(text); else if (s.sink) s.sink.push(text); else s.buf += text;
  }
  P.streamPut = put;
  function pull(s) { if (!s.more) return false; const t = s.more(); if (t == null) { s.more = null; return false; } s.text += t; return true; }
  function readAll(e, st) { const s = streamOf(e, st); while (pull(s)); const t = s.text.slice(s.pos); s.pos = s.text.length; return t; }
  function readLine(e, st) {
    const s = streamOf(e, st);
    while (s.text.indexOf('\n', s.pos) < 0 && pull(s));
    if (s.pos >= s.text.length) return null;
    let i = s.text.indexOf('\n', s.pos); if (i < 0) i = s.text.length;
    let line = s.text.slice(s.pos, i); s.pos = Math.min(s.text.length, i + 1); s.line++;
    if (line.endsWith('\r')) line = line.slice(0, -1);
    return line;
  }
  det('open/3', (a, e) => openStream(a, e, NIL));
  det('open/4', (a, e) => openStream(a, e, a[3]));
  function openStream(a, e, opts) {
    const path = resolvePath(e, textOf(a[0])), mode = textOf(a[1]);
    const id = ++e.streamSeq;
    let s;
    if (mode === 'read') s = { id, mode, path, text: fileText(e, path), pos: 0, line: 1 };
    else if (mode === 'write' || mode === 'append') { const x = io(e); if (!x || !x.writeFile) throw permErr('open', 'source_sink', Atom(path)); s = { id, mode, path, buf: '' }; }
    else throw domErr('io_mode', a[1]);
    for (const o of listToArray(opts) || []) { const t = D(o); if (t.t === 'c' && t.f === 'alias') s.alias = textOf(t.a[0]); }
    e.streams.set(id, s);
    return e.unify(a[2], Cmp('$stream', [Int(id)]));
  }
  function closeStream(e, s) {
    if (!s || s.closed || typeof s.id !== 'number') return;
    s.closed = true; e.streams.delete(s.id);
    if (s.mode === 'write' || s.mode === 'append') ioDo('write', s.path, () => io(e).writeFile(s.path, s.buf, s.mode === 'append'));
  }
  P.closeStreams = (e) => { for (const s of [...e.streams.values()]) closeStream(e, s); };
  det('close/1', (a, e) => { closeStream(e, streamOf(e, a[0])); return true; });
  det('close/2', (a, e) => { closeStream(e, streamOf(e, a[0])); return true; });
  det('read_line_to_string/2', (a, e) => { const l = readLine(e, a[0]); return e.unify(a[1], l === null ? Atom('end_of_file') : Str(l)); });
  det('read_line_to_codes/2', (a, e) => { const l = readLine(e, a[0]); return e.unify(a[1], l === null ? Int(-1) : P.codesList(l)); });
  det('read_string/3', (a, e) => { const t = readAll(e, a[0]); return e.unify(a[1], Int(t.length)) && e.unify(a[2], Str(t)); });
  det('read_string/5', (a, e) => {
    // read_string(+Stream, +SepChars, +PadChars, -Sep, -String)
    const s = streamOf(e, a[0]); const seps = textOf(a[1]), pad = textOf(a[2]);
    if (s.pos >= s.text.length) return e.unify(a[3], Int(-1)) && e.unify(a[4], Str(''));
    let i = s.pos; while (i < s.text.length && !seps.includes(s.text[i])) i++;
    let str = s.text.slice(s.pos, i); const sep = i < s.text.length ? Int(s.text.charCodeAt(i)) : Int(-1); s.pos = Math.min(s.text.length, i + 1);
    let lo = 0, hi = str.length; while (lo < hi && pad.includes(str[lo])) lo++; while (hi > lo && pad.includes(str[hi - 1])) hi--;
    return e.unify(a[3], sep) && e.unify(a[4], Str(str.slice(lo, hi)));
  });
  function readTermFrom(e, st) {
    const s = streamOf(e, st);
    // the next clause: up to a full stop followed by layout or the end
    while (P.nextClauseText(s.text.slice(s.pos)) === s.text.slice(s.pos) && pull(s));
    const rest = s.text.slice(s.pos);
    const toks = P.nextClauseText(rest);
    if (toks === null) { s.pos = s.text.length; return { term: Atom('end_of_file'), vars: [] }; }
    s.pos += toks.length;
    return P.readTerm(toks);
  }
  det('read_term/2', (a, e) => { const r = readTermFrom(e, Atom('user_input')); bindReadOpts(e, a[1], r); return e.unify(a[0], r.term); });
  det('read_term/3', (a, e) => { const r = readTermFrom(e, a[0]); bindReadOpts(e, a[2], r); return e.unify(a[1], r.term); });
  det('read/1', (a, e) => e.unify(a[0], readTermFrom(e, Atom('user_input')).term));
  det('read/2', (a, e) => e.unify(a[1], readTermFrom(e, a[0]).term));
  function bindReadOpts(e, opts, r) {
    for (const o of listToArray(opts) || []) {
      const t = D(o); if (t.t !== 'c' || t.a.length !== 1) continue;
      if (t.f === 'variable_names') e.unify(t.a[0], list((r.vars || []).map(([n, v]) => Cmp('=', [Atom(n), v]))));
      if (t.f === 'variables') e.unify(t.a[0], list((r.vars || []).map(([, v]) => v)));
      // the named variables that appear once (not those starting with _), as Name = Var
      if (t.f === 'singletons') {
        const counts = new Map(); const st = [r.term];
        while (st.length) { const x = D(st.pop()); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') for (const y of x.a) st.push(y); }
        e.unify(t.a[0], list((r.vars || []).filter(([n, v]) => !n.startsWith('_') && counts.get(D(v)) === 1).map(([n, v]) => Cmp('=', [Atom(n), v]))));
      }
    }
  }
  // the text of the next clause in src (through its full stop), or null at the end
  P.nextClauseText = (src) => {
    let i = 0, n = src.length;
    const skipLayout = () => { for (;;) { while (i < n && /\s/.test(src[i])) i++; if (src[i] === '%') { while (i < n && src[i] !== '\n') i++; continue; } if (src[i] === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); i = j < 0 ? n : j + 2; continue; } break; } };
    skipLayout(); if (i >= n) return null;
    while (i < n) {
      const c = src[i];
      if (c === '%') { while (i < n && src[i] !== '\n') i++; continue; }
      if (c === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); i = j < 0 ? n : j + 2; continue; }
      if (c === '"' || c === "'" || c === '`') { i++; while (i < n && src[i] !== c) { if (src[i] === '\\') i++; i++; } i++; continue; }
      if (c === '0' && src[i + 1] === "'") { i += src[i + 2] === '\\' ? 4 : 3; continue; }
      if (c === '.' && (i + 1 >= n || /\s|%/.test(src[i + 1])) && !/[#$&*+\-./:<=>?@^~\\]/.test(src[i - 1] || ' ')) return src.slice(0, i + 1);
      i++;
    }
    return src;
  };
  det('read_file_to_string/3', (a, e) => e.unify(a[1], Str(fileText(e, resolvePath(e, textOf(a[0]))))));
  det('read_file_to_codes/3', (a, e) => e.unify(a[1], P.codesList(fileText(e, resolvePath(e, textOf(a[0]))))));
  det('read_file_to_terms/3', (a, e) => { const cls = P.readProgram(fileText(e, resolvePath(e, textOf(a[0])))); return e.unify(a[1], list(cls.map((c) => c.term))); });
  det('exists_file/1', (a, e) => { const x = io(e); return !!(x && x.stat && x.stat(resolvePath(e, textOf(a[0]))) === 'file'); });
  det('exists_directory/1', (a, e) => { const x = io(e); return !!(x && x.stat && x.stat(resolvePath(e, textOf(a[0]))) === 'dir'); });
  det('directory_files/2', (a, e) => { const x = io(e); const l = x && x.list ? x.list(resolvePath(e, textOf(a[0]))) : null; if (!l) throw existErr('directory', a[0]); return e.unify(a[1], list(['.', '..'].concat(l).map((n) => Atom(n)))); });
  const absOf = (e, p) => { const x = io(e); const r = resolvePath(e, p); if (r.startsWith('/') || /^[A-Za-z]:/.test(r)) return r; return x && x.root ? P.joinPath(x.root, r) : r; };
  det('absolute_file_name/2', (a, e) => e.unify(a[1], Atom(absOf(e, fileSpec(a[0])))));
  det('absolute_file_name/3', (a, e) => {
    let p = fileSpec(a[0]); const x = io(e);
    for (const o of listToArray(a[2]) || []) { const t = D(o); if (t.t === 'c' && t.f === 'extensions') { for (const ext of listToArray(t.a[0]) || []) { const ex = textOf(ext); const c = ex ? p + '.' + ex : p; if (x && x.stat && x.stat(resolvePath(e, c))) { p = c; break; } } } }
    return e.unify(a[1], Atom(absOf(e, p)));
  });
  const fileSpec = (t) => { t = D(t); if (t.t === 'c' && t.a.length === 1 && t.f !== '/') return textOf(t.a[0]); if (t.t === 'c' && t.f === '/' && t.a.length === 2) return fileSpec(t.a[0]) + '/' + fileSpec(t.a[1]); return textOf(t); };
  det('file_directory_name/2', (a, e) => { const p = textOf(a[0]).replace(/\/+$/, ''); const i = p.lastIndexOf('/'); return e.unify(a[1], Atom(i < 0 ? '.' : i === 0 ? '/' : p.slice(0, i))); });
  det('file_base_name/2', (a, e) => { const p = textOf(a[0]); return e.unify(a[1], Atom(p.slice(p.lastIndexOf('/') + 1))); });
  det('file_name_extension/3', (a, e) => {
    const f = D(a[2]);
    if (f.t !== 'v') { const s = textOf(f); const b = s.slice(s.lastIndexOf('/') + 1); const i = b.lastIndexOf('.'); if (i <= 0) return e.unify(a[0], Atom(s)) && e.unify(a[1], Atom('')); return e.unify(a[0], Atom(s.slice(0, s.length - b.length + i))) && e.unify(a[1], Atom(b.slice(i + 1))); }
    const ext = textOf(a[1]).replace(/^\./, ''); return e.unify(f, Atom(ext ? textOf(a[0]) + '.' + ext : textOf(a[0])));
  });
  det('delete_file/1', (a, e) => { const x = io(e); if (!x || !x.deleteFile) throw permErr('delete', 'file', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('delete', p, () => x.deleteFile(p)); return true; });
  det('make_directory/1', (a, e) => { const x = io(e); if (!x || !x.mkdir) throw permErr('create', 'directory', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('create', p, () => x.mkdir(p)); return true; });
  det('working_directory/2', (a, e) => { const x = io(e) || {}; const cur = Atom(((x.cwd || '.') + '/').replace(/\/+$/, '/')); if (!e.unify(a[0], cur)) return false; const n = D(a[1]); if (n.t !== 'v' && x) x.cwd = resolvePath(e, textOf(n)); return true; });
  det('getenv/2', (a, e) => { const x = io(e); const v = x && x.env ? x.env[textOf(a[0])] : undefined; return v != null && e.unify(a[1], Atom(v)); });
  det('shell/1', (a, e) => { const x = io(e); if (!x || !x.shell) throw permErr('execute', 'shell', a[0]); return x.shell(textOf(a[0])) === 0; });
  det('shell/2', (a, e) => { const x = io(e); if (!x || !x.shell) throw permErr('execute', 'shell', a[0]); return e.unify(a[1], Int(x.shell(textOf(a[0])))); });

  // output to streams; as SWI-Prolog lays terms out
  det('write/1', (a, e) => { e.write(SWI(a[0], false)); return true; });
  det('print/1', (a, e) => { e.write(SWI(a[0], true)); return true; });
  det('writeln/1', (a, e) => { e.write(SWI(a[0], false) + '\n'); return true; });
  det('writeq/1', (a, e) => { e.write(SWI(a[0], true)); return true; });
  det('write_canonical/1', (a, e) => { e.write(show(a[0], { quoted: true, ignoreOps: true, swi: !!P.SWI_WRITE })); return true; });
  det('write_term/2', (a, e) => { e.write(show(a[0], { quoted: wtQuoted(a[1]), swi: !!P.SWI_WRITE, nextArg: wtNext(a[1]) })); return true; });
  det('write_term/3', (a, e) => { put(e, a[0], show(a[1], { quoted: wtQuoted(a[2]), swi: !!P.SWI_WRITE, nextArg: wtNext(a[2]) })); return true; });
  const wtNext = (o) => (listToArray(o) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'spacing' && D(x.a[0]).n === 'next_argument'; });
  const wtQuoted = (o) => (listToArray(o) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'quoted' && D(x.a[0]).n === 'true'; });
  det('write/2', (a, e) => { put(e, a[0], SWI(a[1], false)); return true; });
  det('writeln/2', (a, e) => { put(e, a[0], SWI(a[1], false) + '\n'); return true; });
  det('writeq/2', (a, e) => { put(e, a[0], SWI(a[1], true)); return true; });
  det('print/2', (a, e) => { put(e, a[0], SWI(a[1], true)); return true; });
  det('nl/1', (a, e) => { put(e, a[0], '\n'); return true; });
  det('tab/2', (a, e) => { put(e, a[0], ' '.repeat(Number(P.evalArith(a[1]).v))); return true; });
  det('put_char/2', (a, e) => { put(e, a[0], textOf(a[1])); return true; });
  det('flush_output/1', () => true);
  det('format/3', (a, e) => {
    const s = D(a[0]); const txt = P.format(a[1], a[2]);
    if (s.t === 'c' && s.a.length === 1 && ['atom', 'string', 'codes', 'chars'].includes(s.f)) {
      const k = s.f; return e.unify(s.a[0], k === 'atom' ? Atom(txt) : k === 'string' ? Str(txt) : k === 'codes' ? P.codesList(txt) : P.charsList(txt));
    }
    put(e, s, txt); return true;
  });
  det('current_output/1', (a, e) => e.unify(a[0], Atom('user_output')));
  det('current_input/1', (a, e) => e.unify(a[0], Atom('user_input')));
  det('set_stream/2', () => true);
  det('prompt/2', (a, e) => e.unify(a[0], Atom('|: ')));
  det('at_end_of_stream/0', (a, e) => { const s = streamOf(e, Atom('user_input')); if (s.pos >= s.text.length) pull(s); return s.pos >= s.text.length; });
  det('at_end_of_stream/1', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return s.pos >= s.text.length; });
  det('get_char/1', (a, e) => { const s = streamOf(e, Atom('user_input')); if (s.pos >= s.text.length) pull(s); return e.unify(a[0], s.pos < s.text.length ? Atom(s.text[s.pos++]) : Atom('end_of_file')); });
  det('get_char/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], s.pos < s.text.length ? Atom(s.text[s.pos++]) : Atom('end_of_file')); });
  det('peek_char/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], s.pos < s.text.length ? Atom(s.text[s.pos]) : Atom('end_of_file')); });
  det('get_code/2', (a, e) => { const s = streamOf(e, a[0]); if (s.pos >= s.text.length) pull(s); return e.unify(a[1], Int(s.pos < s.text.length ? s.text.charCodeAt(s.pos++) : -1)); });

  // messages, as SWI-Prolog prints an uncaught error or a warning (to user_error)
  det('print_message/2', (a, e) => {
    const kind = textOf(a[0]); if (kind === 'silent' || kind === 'informational') return true;
    e.writeErr((kind === 'error' ? 'ERROR: ' : kind === 'warning' ? 'Warning: ' : '') + messageText(a[1]) + '\n'); return true;
  });
  function messageText(t) {
    t = D(t);
    if (t.t === 'c' && t.f === 'error' && t.a.length === 2) {
      const f = D(t.a[0]);
      if (f.t === 'c' && f.f === 'existence_error' && D(f.a[0]).n === 'procedure') return 'Unknown procedure: ' + SWI(f.a[1], true);
      if (f.t === 'c' && f.f === 'type_error') return 'Type error: `' + SWI(f.a[0], false) + "' expected, found `" + SWI(f.a[1], true) + "'";
      if (f.t === 'a' && f.n === 'instantiation_error') return 'Arguments are not sufficiently instantiated';
      if (f.t === 'c' && f.f === 'evaluation_error') return 'Arithmetic: evaluation error: ' + SWI(f.a[0], true);
      if (f.t === 'c' && f.f === 'existence_error') return SWI(f.a[0], false) + ' `' + SWI(f.a[1], true) + "' does not exist";
      if (f.t === 'c' && f.f === 'syntax_error') return 'Syntax error: ' + SWI(f.a[0], false);
      if (f.t === 'c' && f.f === 'domain_error') return 'Domain error: `' + SWI(f.a[0], false) + "' expected, found `" + SWI(f.a[1], true) + "'";
      return 'Unknown error term: ' + SWI(f, true);
    }
    if (t.t === 'c' && t.f === 'format' && t.a.length === 2) return P.format(t.a[0], t.a[1]);
    return 'Unknown message: ' + SWI(t, true);
  }
  P.messageText = messageText;
  det('message_to_codes/3', (a, e) => e.unify(a[2], P.codesList(messageText(a[0]))));
  // '$messages':translate_message//1 and print_message_lines/3, as print_message/2 uses them
  det('translate_message/3', (a, e) => e.unify(a[1], P.cons(Cmp('-', [Atom('~w'), list([Str(messageText(a[0]))])]), a[2])));
  det('print_message_lines/3', (a, e) => {
    const pre = textOf(a[1]); let line = '', outText = '';
    for (const x of listToArray(a[2]) || []) { const t = D(x); if (t.t === 'a' && t.n === 'nl') { outText += pre + line + '\n'; line = ''; } else if (t.t === 'c' && t.f === '-' && t.a.length === 2) line += P.format(t.a[0], t.a[1]); else if (t.t === 'c' && t.f === 'ansi' && t.a.length === 3) line += P.format(t.a[1], t.a[2]); else line += textOf(t); }
    if (line) outText += pre + line + '\n';
    put(e, a[0], outText); return true;
  });
  // library(csv): rows as row(F1, ...), numbers converted unless convert(false)
  function parseCSV(text, sep) {
    const rows = []; let row = [], f = '', q = false, quoted = false;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (q) { if (c === '"') { if (text[i + 1] === '"') { f += '"'; i++; } else q = false; } else f += c; continue; }
      if (c === '"' && f === '') { q = true; quoted = true; continue; }
      if (c === sep) { row.push({ f, quoted }); f = ''; quoted = false; continue; }
      if (c === '\n' || c === '\r') { if (c === '\r' && text[i + 1] === '\n') i++; row.push({ f, quoted }); rows.push(row); row = []; f = ''; quoted = false; continue; }
      f += c;
    }
    if (f !== '' || quoted || row.length) { row.push({ f, quoted }); rows.push(row); }
    return rows;
  }
  function csvRows(text, opts) {
    let functor = 'row', convert = true, sep = ',', strip = false;
    for (const o of listToArray(opts) || []) { const t = D(o); if (t.t !== 'c' || t.a.length !== 1) continue; const v = D(t.a[0]); if (t.f === 'functor') functor = textOf(v); if (t.f === 'convert') convert = v.n !== 'false'; if (t.f === 'separator') sep = String.fromCharCode(Number(v.v)); if (t.f === 'strip') strip = v.n === 'true'; }
    return parseCSV(text, sep).map((r) => Cmp(functor, r.map(({ f, quoted }) => { if (strip) f = f.trim(); if (convert && !quoted && /^[+-]?\d+(\.\d+)?([eE][+-]?\d+)?$/.test(f)) return /[.eE]/.test(f) ? Num(parseFloat(f), true) : Int(Number(f)); return Atom(f); })));
  }
  det('csv_read_file/2', (a, e) => e.unify(a[1], list(csvRows(fileText(e, resolvePath(e, textOf(a[0]))), NIL))));
  det('csv_read_file/3', (a, e) => e.unify(a[1], list(csvRows(fileText(e, resolvePath(e, textOf(a[0]))), a[2]))));
  det('csv_read_file_row/3', () => false); delete B['csv_read_file_row/3'];
  const csvField = (t) => { const s = textOf(t); return /[",\n\r]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  det('csv_write_file/2', (a, e) => { const x = io(e); const txt = (listToArray(a[1]) || []).map((r) => D(r).a.map(csvField).join(',') + '\r\n').join(''); x.writeFile(resolvePath(e, textOf(a[0])), txt, false); return true; });
  det('csv_write_file/3', (a, e) => B['csv_write_file/2'].fn([a[0], a[1]], e));

  // ---------------------------------------------------------------- the program and the system
  nondet('clause/2', function* (a, e) {
    let h = D(a[0]); if (h.t === 'c' && h.f === ':' && h.a.length === 2) h = D(h.a[1]);
    if (h.t === 'v') throw P.instErr();
    const cls = e.prog.preds.get(P.key(h)); if (!cls) return;
    for (const cl of cls.slice()) { const m = e.mark(); const mp = new Map(); if (e.unify(h, copy(cl.head, mp)) && e.unify(a[1], copy(cl.body, mp))) yield; e.undo(m); }
  });
  nondet('current_predicate/1', function* (a, e) {
    let s = D(a[0]);
    if (s.t === 'c' && s.f === ':' && s.a.length === 2) {
      const m = D(s.a[0]), fa = D(s.a[1]);
      // Module:Name/Arity: the module's own (renamed) predicate, or the plain one it exports
      if (m.t === 'a' && fa.t === 'c' && fa.f === '/' && D(fa.a[0]).t === 'a' && D(fa.a[1]).t === 'n') { const k1 = m.n + ':' + D(fa.a[0]).n + '/' + D(fa.a[1]).v, k2 = D(fa.a[0]).n + '/' + D(fa.a[1]).v; if ((e.prog.preds.get(k1) || []).length || (e.prog.preds.get(k2) || []).length || e.prog.dynamic.has(k1) || e.prog.dynamic.has(k2)) yield 'last'; return; }
      s = fa;
    }
    for (const k of e.prog.order) { if (!e.prog.preds.get(k).length && !e.prog.dynamic.has(k)) continue; const i = k.lastIndexOf('/'); const m = e.mark(); if (e.unify(s, Cmp('/', [Atom(k.slice(0, i)), Int(+k.slice(i + 1))]))) yield; e.undo(m); }
  });
  det('current_predicate/2', (a, e) => { const h = D(a[1]); if (h.t === 'v') return false; return e.prog.preds.has(P.key(h)) && e.unify(a[0], Atom(P.name(h))); });
  det('predicate_property/2', (a, e) => { let h = D(a[0]); if (h.t === 'c' && h.f === ':') h = D(h.a[1]); if (h.t === 'v') return false; const k = P.key(h); if (B[k] || P.CONTROL.has(k)) return e.unify(a[1], Atom('built_in')) || e.unify(a[1], Atom('defined')); if (!e.prog.preds.has(k)) return false; const p = D(a[1]); if (p.t === 'v') return e.unify(p, Atom('defined')); if (p.t === 'a' && p.n === 'dynamic') return e.prog.dynamic.has(k); if (p.t === 'c' && p.f === 'number_of_clauses') return e.unify(p.a[0], Int(e.prog.preds.get(k).length)); return p.t === 'a' && (p.n === 'defined' || p.n === 'visible'); });
  nondet('current_prolog_flag/2', function* (a, e) {
    const x = io(e) || {};
    const flags = [['argv', list((x.argv || []).map((s) => Atom(s)))], ['bounded', Atom('false')], ['dialect', Atom('swi')], ['version', Int(90000)], ['max_tagged_integer', Int(1152921504606846975)], ['min_tagged_integer', Int(-1152921504606846976)], ['double_quotes', Atom('codes')], ['os_argv', list(['swipl'].concat(x.argv || []).map((s) => Atom(s)))], ['executable', Atom('pl2detlog')], ['home', Atom('.')], ['unix', Atom('true')], ['encoding', Atom('utf8')]];
    for (const [k, v] of flags) { const m = e.mark(); if (e.unify(a[0], Atom(k)) && e.unify(a[1], v)) yield; e.undo(m); }
  });
  det('prolog_load_context/2', (a, e) => { const x = io(e) || {}; const k = textOf(a[0]); if (k === 'directory') return e.unify(a[1], Atom(x.loadDir || x.cwd || '.')); if (k === 'module') return e.unify(a[1], Atom('user')); return false; });
  // loading files while the program runs (as mnnaction loads mnns): the clauses are added to the
  // program and its directives run; library(...) modules are built in
  function loadAtRun(e, spec0) {
    let spec = D(spec0); if (spec.t === 'c' && spec.f === ':' && spec.a.length === 2) spec = D(spec.a[1]);
    if (spec.t === 'c' && spec.f === 'library') return true;
    for (const one of listToArray(spec) || [spec]) {
      let f = D(one); if (f.t === 'c' && f.f === ':' && f.a.length === 2) f = D(f.a[1]);
      if (f.t === 'c' && f.f === 'library') continue;
      const x = io(e) || {}, base = resolvePath(e, textOf(f));
      const path = [base, base + '.pl', base + '.pro'].find((c) => x.stat ? x.stat(c) === 'file' : x.readFile && x.readFile(c) != null);
      if (!path) throw existErr('source_sink', f);
      e.loaded = e.loaded || new Set(); if (e.loaded.has(path)) continue; e.loaded.add(path);
      const text = x.readFile(path), dir = path.replace(/\/[^/]*$/, '');
      const saveCwd = x.loadDir; x.loadDir = dir;
      try {
        let cls = P.readProgram(text); const fwds = [];
        // the module directive: the first directive that is one, before any clause (after :- encoding(..) say)
        let md = null; for (const c of cls) { const t0 = D(c.term); if (!(t0.t === 'c' && t0.f === ':-' && t0.a.length === 1)) break; const d0 = D(t0.a[0]); if (d0.t === 'c' && d0.f === 'module' && d0.a.length === 2) { md = d0; break; } }
        if (md && md.t === 'c' && md.f === 'module' && md.a.length === 2) {
          const r = P.renameModule(cls.map((c) => c.term), P.textOf(md.a[0]), P.moduleExports(md));
          P.notePrivates(e.prog, P.textOf(md.a[0]), r.privates);
          for (const fw of r.forwarders) if (!(e.prog.preds.get(fw.key) || []).length) { const added = e.prog.add(fw.clause); if (added) fwds.push(added); }
          (e.prog.moduleFiles = e.prog.moduleFiles || new Map()).set(P.textOf(md.a[0]), path);
          cls = cls.map((c, i) => ({ term: r.terms[i], vars: c.vars }));
        }
        e.loadedClauses = e.loadedClauses || new Map(); const mine = fwds; e.loadedClauses.set(path, mine);
        const inits = [];
        // term_expansion/2 and goal_expansion/2, as SWI-Prolog applies them while it loads (Starlog's)
        cls = expandClauses(e, cls);
        for (const c of cls) {
          const t = D(c.term);
          if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
            const d = D(t.a[0]), n = d.t === 'c' ? d.f : d.t === 'a' ? d.n : '';
            if (['module', 'use_module', 'ensure_loaded', 'consult', 'include', 'load_files', 'reexport'].includes(n)) {
              if (n !== 'module') { const sv = x.cwd; x.cwd = dir; try { loadAtRun(e, d.a[0]); } finally { x.cwd = sv; } }
              continue;
            }
            if (n === 'dynamic' || n === 'discontiguous') { for (const s2 of P.commaList(d.a[0])) { const sd = D(s2); if (sd.t === 'c' && sd.f === '/') { const k = P.name(sd.a[0]) + '/' + D(sd.a[1]).v; if (n === 'dynamic') e.prog.dynamic.add(k); if (!e.prog.preds.has(k)) { e.prog.preds.set(k, []); e.prog.order.push(k); } } } continue; }
            if (n === 'initialization') { inits.push(d.a[0]); continue; } // run when the file is loaded
            if (['set_prolog_flag', 'license', 'meta_predicate', 'multifile', 'table', 'module_transparent', 'public', 'encoding', 'style_check'].includes(n)) continue;
            e.solve(d, () => false);
            continue;
          }
          const added = e.prog.add(t, c.vars); if (added) mine.push(added);
        }
        for (const g of inits) { const m = e.mark(); e.solve(g, () => false); e.undo(m); }
      } finally { x.loadDir = saveCwd; }
    }
    return true;
  }
  const hasClauses = (e, k) => (e.prog.preds.get(k) || []).length > 0;
  function callOnce(e, goal, out) {
    const m = e.mark(); let r = null;
    try { e.solve(goal, () => { r = P.copy(P.resolve(out)); return false; }); } catch (x) { if (x && x.halt) throw x; r = null; }
    e.undo(m); return r;
  }
  function expandGoals(e, g, depth = 0) {
    g = D(g);
    if (g.t === 'v' || depth > 40) return g;
    const k = P.key(g); if (!k) return g;
    if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = expandGoals(e, a[i], depth); return { t: 'c', f: g.f, a }; }
    const X = Var(), r = callOnce(e, Cmp('goal_expansion', [g, X]), Cmp('x', [g, X]));
    if (r && !P.variant(D(r.a[1]), g)) { return expandGoals(e, D(r.a[1]), depth + 1); }
    return g;
  }
  P.variant = (a, b) => P.variantKey(a) === P.variantKey(b);
  function expandClauses(e, cls) {
    const te = hasClauses(e, 'term_expansion/2'), ge = hasClauses(e, 'goal_expansion/2');
    if (!te && !ge) return cls;
    const out = [];
    for (const c of cls) {
      let ts = [c.term];
      const t0 = D(c.term);
      const directive = t0.t === 'c' && t0.f === ':-' && t0.a.length === 1;
      if (te && !directive) {
        const X = Var(); const r = callOnce(e, Cmp('term_expansion', [c.term, X]), Cmp('x', [c.term, X]));
        if (r) { const x = D(r.a[1]); ts = listToArray(x) || [x]; }
      }
      for (let t of ts) {
        t = D(t);
        if (ge) {
          if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = Cmp(':-', [t.a[0], expandGoals(e, t.a[1])]);
          else if (t.t === 'c' && t.f === ':-' && t.a.length === 1) t = Cmp(':-', [expandGoals(e, t.a[0])]);
        }
        out.push({ term: t, vars: c.vars });
      }
    }
    return out;
  }
  P.expandClauses = expandClauses;
  det('expand_goal/2', (a, e) => e.unify(a[1], hasClauses(e, 'goal_expansion/2') ? expandGoals(e, a[0]) : a[0]));
  det('expand_term/2', (a, e) => { if (!hasClauses(e, 'term_expansion/2')) return e.unify(a[1], a[0]); const X = Var(); const r = callOnce(e, Cmp('term_expansion', [a[0], X]), Cmp('x', [a[0], X])); return e.unify(a[1], r ? r.a[1] : a[0]); });
  det('consult/1', (a, e) => loadAtRun(e, a[0]));
  det('ensure_loaded/1', (a, e) => loadAtRun(e, a[0]));
  det('use_module/1', (a, e) => loadAtRun(e, a[0]));
  det('use_module/2', (a, e) => loadAtRun(e, a[0]));
  det('load_files/2', (a, e) => loadAtRun(e, a[0]));
  det('module/2', () => true);
  det('=@=/2', (a) => P.variantKey(a[0]) === P.variantKey(a[1]));
  det('\\=@=/2', (a) => P.variantKey(a[0]) !== P.variantKey(a[1]));
  det('op/3', (a) => { P.applyOpDirective(Cmp('op', a)); return true; });
  det('set_prolog_flag/2', () => true);
  det('license/1', () => true);
  det('initialization/1', () => true);
  det('initialization/2', () => true);
  det('table/1', () => true);
  det('meta_predicate/1', () => true);
  det('multifile/1', () => true);
  det('module_transparent/1', () => true);
  det('public/1', () => true);
  det('nb_current/2', (a, e) => { const k = D(a[0]); if (k.t === 'v') return false; const v = e.globals.get(textOf(k)); return !!v && e.unify(a[1], v); });
  det('tmp_file/2', (a, e) => e.unify(a[1], Atom('/tmp/pl_' + textOf(a[0]) + '_' + (++e.streamSeq))));
  det('ground/1', (a) => isGround(a[0]));
  det('string_code/3', (a, e) => { const i = Number(P.evalArith(a[0]).v), s = textOf(a[1]); return i >= 1 && i <= s.length && e.unify(a[2], Int(s.charCodeAt(i - 1))); });
  det('sumlist/2', B['sum_list/2'].fn);
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(SWI(t, true))); const r = P.readTerm(textOf(a[1])); return e.unify(t, r.term); });
  det('with_output_to_string/2', () => false); delete B['with_output_to_string/2'];
  det('ansi_format/3', (a, e) => { e.write(P.format(a[1], a[2])); return true; });
  det('sleep/1', () => true);
  det('shell/0', () => true);
  det('garbage_collect_atoms/0', () => true);
  det('statistics/0', () => true);
  det('assertion/1', () => true); // replaced by the prelude's definition
  delete B['assertion/1'];
  callb(':/2', (a, e) => {
    const m = D(a[0]), g = D(a[1]);
    if (m.t === 'a' && (g.t === 'a' || g.t === 'c')) { const f = g.t === 'a' ? g.n : g.f, n = g.t === 'a' ? 0 : g.a.length; const pk = m.n + ':' + f + '/' + n; if (e.prog.preds.has(pk)) return g.t === 'a' ? Atom(m.n + ':' + f) : { t: 'c', f: m.n + ':' + f, a: g.a };
      // a library module (lists, apply, ..: not one the program loaded): its built-in, not a user predicate of that name
      if (g.t === 'c' && B[f + '/' + n] && m.n !== 'user' && !(e.prog.moduleFiles && e.prog.moduleFiles.has(m.n))) return { t: 'c', f: g.f, a: g.a, lib: true }; }
    return g;
  });
  callb('setup_call_cleanup/3', (a) => Cmp('$scc', [a[0], a[1], a[2]]));
  callb('call_cleanup/2', (a) => Cmp('$scc', [Atom('true'), a[0], a[1]]));

  // ---- modules: a module's private predicates are renamed 'Module:name', so that two modules can
  // each have their own helper of the same name; exported predicates keep their names. Calls in the
  // module (and in its meta-arguments: maplist(helper, ...), findall(_, helper(..), _), lambdas)
  // are renamed with them; Module:Goal calls Module's own; a goal built at run time that names a
  // private predicate finds it through prog.privates.
  const CLOSURE_EXTRA = { 'maplist/2': 1, 'maplist/3': 2, 'maplist/4': 3, 'maplist/5': 4, 'maplist/6': 5, 'maplist/7': 6, 'foldl/4': 3, 'foldl/5': 4, 'foldl/6': 5, 'foldl/7': 6, 'include/3': 1, 'exclude/3': 1, 'partition/4': 1, 'partition/6': 2, 'convlist/3': 2, 'max_member/3': 2, 'min_member/3': 2, 'predsort/3': 3, 'map_list_to_pairs/3': 2, 'call/2': 1, 'call/3': 2, 'call/4': 3, 'call/5': 4, 'call/6': 5, 'call/7': 6, 'call/8': 7, 'aggregate_all/3': -1 };
  const GOAL_POS = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'not/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'catch/3': [0, 2], '^/2': [1], 'with_output_to/2': [1], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1], 'time/1': [0], 'call_with_time_limit/2': [1], 'call_with_inference_limit/3': [0], 'with_mutex/2': [1], 'tabled_call/1': [0], 'phrase/2': [], 'phrase/3': [], 'initialization/1': [0], 'initialization/2': [0] };
  const DBK = new Set(['assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'retractall/1', 'clause/2', 'abolish/1']);
  function renameModule(terms, M, exportKeys) {
    const local = new Set();
    const headKey = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); while (t.t === 'c' && t.f === ':' && t.a.length === 2) t = D(t.a[1]); if (t.t === 'c' && t.f === '-->' && t.a.length === 2) { let h = D(t.a[0]); if (h.t === 'c' && h.f === ',') h = D(h.a[0]); const k = P.key(h); if (!k) return null; const i = k.lastIndexOf('/'); return k.slice(0, i) + '/' + (+k.slice(i + 1) + 2); } return P.key(t); };
    // a clause whose head names another module (user:term_expansion(..)) belongs to that module: it keeps its name
    const foreign = (t) => { t = D(t); if (t.t === 'c' && t.f === ':-' && t.a.length === 2) t = D(t.a[0]); return t.t === 'c' && t.f === ':' && t.a.length === 2 && D(t.a[0]).t === 'a' && D(t.a[0]).n !== M; };
    for (const t of terms) { if (foreign(t)) continue; const d = D(t); if (d.t === 'c' && d.f === ':-' && d.a.length === 1) { const g = D(d.a[0]); if (g.t === 'c' && (g.f === 'dynamic' || g.f === 'discontiguous' || g.f === 'table')) for (const x of P.commaList(g.a[0])) { const sd = D(x); if (sd.t === 'c' && sd.f === '/' && D(sd.a[0]).t !== 'c') local.add(P.name(sd.a[0]) + '/' + D(sd.a[1]).v); } continue; } const k = headKey(t); if (k) local.add(k); }
    // every predicate of the module is renamed (so the module always calls its own); an exported one
    // also gets a plain-named forwarder (the first module to export a name keeps it). Dynamic ones that
    // are exported keep their plain name, as other modules may assert them.
    const dyn = new Set();
    for (const t of terms) { const d = D(t); if (d.t === 'c' && d.f === ':-' && d.a.length === 1) { const g = D(d.a[0]); if (g.t === 'c' && g.f === 'dynamic') for (const x of P.commaList(g.a[0])) { const sd = D(x); if (sd.t === 'c' && sd.f === '/') dyn.add(P.name(sd.a[0]) + '/' + D(sd.a[1]).v); } } }
    const priv = new Set([...local].filter((k) => !(exportKeys.has(k) && dyn.has(k))));
    if (!priv.size) return { terms, privates: [], forwarders: [] };
    const rn = (name) => M + ':' + name;
    const renameHead = (h) => { h = D(h); if (h.t === 'c' && h.f === ':' && h.a.length === 2 && D(h.a[0]).t === 'a' && D(h.a[0]).n !== M) return D(h.a[1]); while (h.t === 'c' && h.f === ':' && h.a.length === 2) h = D(h.a[1]); const k = P.key(h); if (!priv.has(k)) return h; return h.t === 'a' ? Atom(rn(h.n)) : { t: 'c', f: rn(h.f), a: h.a }; };
    const closure = (c, extra) => {
      c = D(c);
      if (c.t === 'c' && c.f === '>>' && c.a.length === 2) return { t: 'c', f: '>>', a: [c.a[0], goal(c.a[1])] };
      if (c.t === 'c' && c.f === ':' && c.a.length === 2) return qualified(c);
      const k = c.t === 'a' ? c.n + '/' + extra : c.t === 'c' ? c.f + '/' + (c.a.length + extra) : null;
      if (!k || !priv.has(k)) return c;
      return c.t === 'a' ? Atom(rn(c.n)) : { t: 'c', f: rn(c.f), a: c.a };
    };
    const qualified = (g) => { const m = D(g.a[0]); if (m.t === 'a' && m.n === M) return goal(g.a[1]); return g; };
    function goal(g) {
      g = D(g);
      if (g.t === 'v') return g;
      if (g.t === 'c' && g.f === ':' && g.a.length === 2) return qualified(g);
      const k = P.key(g); if (!k) return g;
      if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = goal(a[i]); if (k === 'phrase/2' || k === 'phrase/3') a[0] = closure(a[0], 2); return { t: 'c', f: g.f, a }; }
      if (CLOSURE_EXTRA[k] > 0) { const a = g.a.slice(); a[0] = closure(a[0], CLOSURE_EXTRA[k]); return { t: 'c', f: g.f, a }; }
      if (g.t === 'c' && g.f === '>>') return { t: 'c', f: '>>', a: [g.a[0], goal(g.a[1])].concat(g.a.slice(2)) };
      if (DBK.has(k) && g.a.length) { const a = g.a.slice(); a[0] = dbArg(a[0]); return { t: 'c', f: g.f, a }; }
      if (priv.has(k)) return g.t === 'a' ? Atom(rn(g.n)) : { t: 'c', f: rn(g.f), a: g.a };
      return g;
    }
    // assert(foo(..)), retract((foo(..) :- B)): the clause's head names a predicate of the module
    function dbArg(c) { c = D(c); if (c.t === 'c' && c.f === ':-' && c.a.length === 2) return Cmp(':-', [renameHead(c.a[0]), goal(c.a[1])]); if (c.t === 'c' && c.f === ':' && c.a.length === 2) return c; return c.t === 'v' ? c : renameHead(c); }
    const out = terms.map((t) => {
      const d = D(t);
      if (d.t === 'c' && d.f === ':-' && d.a.length === 2) return Cmp(':-', [renameHead(d.a[0]), goal(d.a[1])]);
      if (d.t === 'c' && d.f === ':-' && d.a.length === 1) {
        const g = D(d.a[0]);
        if (g.t === 'c' && (g.f === 'dynamic' || g.f === 'discontiguous' || g.f === 'table')) return Cmp(':-', [Cmp(g.f, [P.conj(P.commaList(g.a[0]).map((x) => { const sd = D(x); return sd.t === 'c' && sd.f === '/' && priv.has(P.name(sd.a[0]) + '/' + D(sd.a[1]).v) ? Cmp('/', [Atom(rn(P.name(sd.a[0]))), sd.a[1]]) : sd; }))])]);
        return Cmp(':-', [goal(g)]);
      }
      if (d.t === 'c' && d.f === '-->' && d.a.length === 2) { const tr = P.dcgTransform(d); return Cmp(':-', [renameHead(tr.a[0]), goal(tr.a[1])]); }
      return renameHead(d);
    });
    const forwarders = [...priv].filter((k) => exportKeys.has(k)).map((k) => { const i = k.lastIndexOf('/'), f = k.slice(0, i), n = +k.slice(i + 1); const vs = Array.from({ length: n }, () => Var()); return { key: k, clause: n ? Cmp(':-', [Cmp(f, vs), Cmp(rn(f), vs)]) : Cmp(':-', [Atom(f), Atom(rn(f))]) }; });
    return { terms: out, privates: [...priv].filter((k) => !exportKeys.has(k)), forwarders };
  }
  P.renameModule = renameModule;
  P.moduleExports = (d) => { const ex = new Set(); for (const x of listToArray(D(d).a[1]) || []) { const t = D(x); if (t.t === 'c' && (t.f === '/' || t.f === '//') && t.a.length === 2) ex.add(P.name(t.a[0]) + '/' + (Number(D(t.a[1]).v) + (t.f === '//' ? 2 : 0))); } return ex; };
  P.notePrivates = (prog, M, privs) => { prog.privates = prog.privates || new Map(); for (const k of privs) { const i = k.lastIndexOf('/'); const plain = k.slice(0, i) + '/' + k.slice(i + 1); if (!prog.privates.has(plain)) prog.privates.set(plain, []); prog.privates.get(plain).push(M + ':' + k.slice(0, i)); } };

  // ---- functional notation on dicts: a goal with Dict.Func in it first evaluates ./3
  const hasDots = (t) => { t = D(t); return t.t === 'c' && (t.f === '$dot' && t.a.length === 2 || t.a.some(hasDots)); };
  P.hasDots = hasDots;
  const GOALARGS = { ',/2': [0, 1], ';/2': [0, 1], '->/2': [0, 1], '*->/2': [0, 1], '\\+/1': [0], 'call/1': [0], 'once/1': [0], 'ignore/1': [0], 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'bagof/3': [1], 'setof/3': [1], 'aggregate_all/3': [1], 'catch/3': [0, 2], '^/2': [1] };
  function pullDots(t, pre) {
    t = D(t);
    if (t.t !== 'c') return t;
    const args = t.a.map((x) => pullDots(x, pre));
    if (t.f === '$dot' && t.a.length === 2) { const V = Var(); pre.push(Cmp('.', [args[0], args[1], V])); return V; }
    return { t: 'c', f: t.f, a: args };
  }
  function expandGoal(g) {
    g = D(g);
    if (g.t !== 'c') return g;
    const k = g.f + '/' + g.a.length;
    if (GOALARGS[k]) { const a = g.a.slice(); for (const i of GOALARGS[k]) a[i] = expandGoal(a[i]); for (let i = 0; i < a.length; i++) if (!GOALARGS[k].includes(i) && hasDots(a[i])) { const pre = []; a[i] = pullDots(a[i], pre); if (pre.length) return P.conj(pre.concat([{ t: 'c', f: g.f, a }])); } return { t: 'c', f: g.f, a }; }
    if (!hasDots(g)) return g;
    const pre = []; const ng = pullDots(g, pre);
    return P.conj(pre.concat([ng]));
  }
  P.expandDots = (cl) => {
    cl = D(cl);
    let h = cl, b = Atom('true');
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) { h = D(cl.a[0]); b = cl.a[1]; }
    else if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 1) return Cmp(':-', [expandGoal(cl.a[0])]);
    const pre = []; h = pullDots(h, pre);
    const body = expandGoal(b);
    return Cmp(':-', [h, pre.length ? P.conj(pre.concat([body])) : body]);
  };
  det('./3', (a, e) => {
    const d = D(a[0]), f = D(a[1]);
    if (f.t === 'a' || f.t === 'n') { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, f) === 0); if (!p) throw err(Cmp('existence_error', [Atom('key'), f, d])); return e.unify(a[2], p[1]); }
    if (f.t === 'c' && f.f === 'get' && f.a.length === 1) { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, D(f.a[0])) === 0); return !!p && e.unify(a[2], p[1]); }
    if (f.t === 'c' && f.f === 'get' && f.a.length === 2) { const ps = dictOf(d); const p = ps.find(([k]) => compare(k, D(f.a[0])) === 0); return e.unify(a[2], p ? p[1] : f.a[1]); }
    if (f.t === 'c' && f.f === 'put' && f.a.length === 1) return B['put_dict/3'].fn([f.a[0], d, a[2]], e);
    if (f.t === 'c' && f.f === 'put' && f.a.length === 2) return B['put_dict/4'].fn([f.a[0], d, f.a[1], a[2]], e);
    throw err(Cmp('existence_error', [Atom('dict_function'), f]));
  });

  // ---- more of SWI-Prolog's library (as mnns uses it)
  nondet('stream_property/2', function* (a, e) {
    const s = streamOf(e, a[0]);
    const props = [Cmp('mode', [Atom(s.mode || 'read')])];
    if (s.path) props.push(Cmp('file_name', [Atom(s.path)]));
    if (s.alias) props.push(Cmp('alias', [Atom(s.alias)]));
    if (s.text !== undefined) props.push(Cmp('position', [Cmp('$stream_position', [Int(s.pos), Int(s.line || 1), Int(0), Int(s.pos)])]));
    if (s.mode === 'read') props.push(Atom('input')); else props.push(Atom('output'));
    props.push(Cmp('encoding', [Atom('utf8')]));
    for (const p of props) { const m = e.mark(); if (e.unify(a[1], p)) yield; e.undo(m); }
  });
  det('stream_position_data/3', (a, e) => { const f = textOf(a[0]), p = D(a[1]); if (p.t !== 'c') return false; const i = { char_count: 0, line_count: 1, line_position: 2, byte_count: 3 }[f]; return i !== undefined && e.unify(a[2], p.a[i]); });
  det('set_stream_position/2', (a, e) => { const s = streamOf(e, a[0]); const p = D(a[1]); s.pos = Number(D(p.a[0]).v); s.line = Number(D(p.a[1]).v); return true; });
  det('line_count/2', (a, e) => e.unify(a[1], Int(streamOf(e, a[0]).line || 1)));
  det('open_string/2', (a, e) => { const id = ++e.streamSeq; e.streams.set(id, { id, mode: 'read', text: textOf(a[0]), pos: 0, line: 1 }); return e.unify(a[1], Cmp('$stream', [Int(id)])); });
  det('tmp_file_stream/3', (a, e) => {
    const x = io(e); if (!x || !x.writeFile) throw permErr('open', 'source_sink', Atom('tmp'));
    const path = (x.tmpDir || '/tmp').replace(/\/$/, '') + '/pl2d_' + Date.now().toString(36) + '_' + (++e.streamSeq) + '.pl';
    x.writeFile(path, '', false);
    const id = ++e.streamSeq; e.streams.set(id, { id, mode: 'write', path, buf: '' });
    return e.unify(a[1], Atom(path)) && e.unify(a[2], Cmp('$stream', [Int(id)]));
  });
  det('rename_file/2', (a, e) => { const x = io(e); if (!x || !x.rename) throw permErr('rename', 'file', a[0]); const p = resolvePath(e, textOf(a[0])); ioDo('rename', p, () => x.rename(p, resolvePath(e, textOf(a[1])))); return true; });
  det('unload_file/1', (a, e) => {
    const path = resolvePath(e, textOf(a[0])); const cls = e.loadedClauses && e.loadedClauses.get(path); if (!cls) return true;
    for (const cl of cls) { const k = P.key(cl.head); const l = e.prog.preds.get(k); if (l) { const i = l.indexOf(cl); if (i >= 0) l.splice(i, 1); if (!l.length && !e.prog.dynamic.has(k)) { e.prog.preds.delete(k); const j = e.prog.order.indexOf(k); if (j >= 0) e.prog.order.splice(j, 1); } } }
    e.loadedClauses.delete(path); if (e.loaded) e.loaded.delete(path); return true;
  });
  nondet('sub_term/2', function* (a, e) {
    const all = []; (function walk(t) { t = D(t); all.push(t); if (t.t === 'c') t.a.forEach(walk); })(a[1]);
    for (const t of all) { const m = e.mark(); if (e.unify(a[0], t)) yield; e.undo(m); }
  });
  det('compound_name_arguments/3', (a, e) => { const t = D(a[0]); if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], list(t.a)); const args = listToArray(a[2]) || []; return e.unify(t, { t: 'c', f: textOf(a[1]), a: args }); });
  det('compound_name_arity/3', (a, e) => { const t = D(a[0]); if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], Int(t.a.length)); const n = Number(D(a[2]).v); return e.unify(t, { t: 'c', f: textOf(a[1]), a: Array.from({ length: n }, () => Var()) }); });
  det('acyclic_term/1', () => true);
  det('cyclic_term/1', () => false);
  nondet('current_module/1', function* (a, e) { for (const m of ['user', 'system']) { const k = e.mark(); if (e.unify(a[0], Atom(m))) yield; e.undo(k); } });
  nondet('module_property/2', function* (a, e) {
    const files = e.prog.moduleFiles || new Map(); const m = D(a[0]);
    for (const [mod, f] of files) { if (m.t !== 'v' && m.n !== mod) continue; const k = e.mark(); if (e.unify(a[0], Atom(mod)) && e.unify(a[1], Cmp('file', [Atom(f)]))) yield; e.undo(k); }
  });
  det('set_random/1', () => true);
  det('directory_file_path/3', (a, e) => { const d = D(a[0]), f = D(a[1]); if (d.t !== 'v' && f.t !== 'v') return e.unify(a[2], Atom(P.joinPath(textOf(d), textOf(f)))); const p = textOf(a[2]); const i = p.lastIndexOf('/'); return e.unify(d, Atom(i < 0 ? '.' : p.slice(0, i))) && e.unify(f, Atom(p.slice(i + 1))); });
  det('numbervars/4', (a, e) => {
    const single = (listToArray(a[3]) || []).some((x) => { x = D(x); return x.t === 'c' && x.f === 'singletons' && D(x.a[0]).n === 'true'; });
    let n = Number(D(a[1]).v);
    const counts = new Map(); (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(a[0]);
    for (const v of P.termVars(a[0])) e.bind(v, Cmp('$VAR', [single && counts.get(v) === 1 ? Atom('_') : Int(n++)]));
    return e.unify(a[2], Int(n));
  });
  // as SWI-Prolog's portray_clause/1 lays a clause out: variables A, B, ... (one seen once is _),
  // one goal a line, disjunctions and if-then-else in columns, meta-arguments that are control
  // constructs one argument a line
  const PC_META = { 'findall/3': [1], 'findall/4': [1], 'forall/2': [0, 1], 'aggregate_all/3': [1], 'aggregate_all/4': [2], 'bagof/3': [1], 'setof/3': [1], 'once/1': [0], 'ignore/1': [0], '\\+/1': [0], 'call/1': [0], 'catch/3': [0, 2], 'with_output_to/2': [1], 'time/1': [0], 'setup_call_cleanup/3': [0, 1, 2], 'call_cleanup/2': [0, 1] };
  const isControl = (g) => { g = D(g); return g.t === 'c' && g.a.length === 2 && (g.f === ',' || g.f === ';' || g.f === '->' || g.f === '*->'); };
  function portray(t) {
    const c = P.copy(t);
    const counts = new Map(); (function walk(x) { x = D(x); if (x.t === 'v') counts.set(x, (counts.get(x) || 0) + 1); else if (x.t === 'c') x.a.forEach(walk); })(c);
    const names = new Map(); let n = 0;
    const o = { quoted: true, swi: true, nextArg: true, varName: (v) => { if (counts.get(v) === 1) return '_'; if (!names.has(v)) names.set(v, P.letters(n++)); return names.get(v); } };
    const pad = (k) => ' '.repeat(k);
    const term = (x, prec) => show(x, Object.assign({ prec }, o));
    // a goal at column col (the text starts there; later lines are indented from col)
    function goal(g, col) {
      g = D(g);
      if (g.t === 'c' && g.a.length === 2 && (g.f === ';' || g.f === '->' || g.f === '*->')) return disj(g, col);
      const k = P.key(g);
      if (k === '\\+/1' && isControl(g.a[0])) return '\\+' + block(g.a[0], col + 2);
      if (PC_META[k] && PC_META[k].some((i) => isControl(g.a[i]))) {
        const nm = P.fmtAtom(g.f, true) + '(', c2 = col + nm.length;
        if (g.a.length === 1) return nm + block(g.a[0], c2) + ')';
        return nm + g.a.map((x, i) => (i ? pad(c2) : '') + (PC_META[k].includes(i) && isControl(x) ? block(x, c2) : term(x, 999))).join(',\n') + ')';
      }
      return term(g, 999);
    }
    function conjAt(g, col) { const gs = P.commaList(g).length ? flat(g) : [g]; return gs.map((x, i) => (i ? pad(col) : '') + goal(x, col)).join(',\n'); }
    function flat(g) { g = D(g); return g.t === 'c' && g.f === ',' && g.a.length === 2 ? flat(g.a[0]).concat(flat(g.a[1])) : [g]; }
    function block(g, col) {
      g = D(g);
      if (g.t === 'c' && g.f === ',' && g.a.length === 2) return '( ' + conjAt(g, col + 2) + '\n' + pad(col) + ')';
      if (g.t === 'c' && g.a.length === 2 && (g.f === ';' || g.f === '->' || g.f === '*->')) return disj(g, col);
      return goal(g, col);
    }
    function disj(g, col) {
      const parts = [];
      (function alt(x, first) {
        x = D(x);
        if (x.t === 'c' && x.f === ';' && x.a.length === 2) { alt(x.a[0], first); alt(x.a[1], false); return; }
        const lead = first ? '(   ' : ';   ';
        if (x.t === 'c' && (x.f === '->' || x.f === '*->') && x.a.length === 2) { parts.push(lead + conjAt(x.a[0], col + 4)); parts.push((x.f === '->' ? '->  ' : '*-> ') + conjAt(x.a[1], col + 4)); return; }
        parts.push(lead + conjAt(x, col + 4));
      })(g, true);
      return parts.map((p, i) => (i ? pad(col) : '') + p).join('\n') + '\n' + pad(col) + ')';
    }
    const d = D(c);
    if (d.t === 'c' && d.f === ':-' && d.a.length === 2) {
      const b = D(d.a[1]);
      if (b.t === 'a' && b.n === 'true') return term(d.a[0], 1199) + '.\n';
      return term(d.a[0], 1199) + ' :-\n' + pad(4) + conjAt(b, 4) + '.\n';
    }
    if (d.t === 'c' && d.f === ':-' && d.a.length === 1) return ':- ' + conjAt(d.a[0], 3) + '.\n';
    return term(d, 1199) + '.\n';
  }
  P.portrayClause = portray;
  det('portray_clause/1', (a, e) => { e.write(portray(a[0])); return true; });
  det('portray_clause/2', (a, e) => { put(e, a[0], portray(a[1])); return true; });
  det('call_with_depth_limit/3', () => false); delete B['call_with_depth_limit/3'];
  callb('with_mutex/2', (a) => Cmp('once', [a[1]]));
  // term_string/3 and term_to_atom with read options (variable_names(Vs), variables(Vs))
  const readOpts = (e, opts, r) => bindReadOpts(e, opts, r);
  det('term_string/3', (a, e) => { const t = D(a[0]); const s0 = D(a[1]); if (s0.t === 'v') return e.unify(s0, Str(SWI(t, true))); const r = P.readTerm(textOf(s0)); if (P.hasDots(r.term)) r.term = P.expandDots(Cmp(':-', [Atom('$t'), r.term])).a[1]; readOpts(e, a[2], r); return e.unify(t, r.term); });
  det('term_string/2', (a, e) => { const t = D(a[0]); const s0 = D(a[1]); if (s0.t === 'v') return e.unify(s0, Str(SWI(t, true))); return e.unify(t, P.readTerm(textOf(s0)).term); });
  det('read_term_from_atom/3', (a, e) => { const r = P.readTerm(textOf(a[0])); readOpts(e, a[2], r); return e.unify(a[1], r.term); });
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v' && D(a[1]).t === 'v') return e.unify(a[1], Atom(SWI(t, true))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('flag/3', (a, e) => { e.flags3 = e.flags3 || new Map(); const k = show(a[0], { quoted: true }); const old = e.flags3.get(k) || Int(0); if (!e.unify(a[1], old)) return false; const n = D(a[2]); e.flags3.set(k, n.t === 'n' ? n : P.evalArith(n)); return true; });
  // ---- clauses asserted into a module (assertz(M:Clause)): the head becomes 'M:name' and each call
  // in the body M:Goal, which finds M's own predicate first (as a module's clauses would)
  const SYSMOD = new Set(['user', 'system', 'lists', 'apply']);
  function intoModule(M, cl) {
    cl = D(cl);
    let h = cl, b = null;
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) { h = D(cl.a[0]); b = cl.a[1]; }
    const hh = h.t === 'a' ? Atom(M + ':' + h.n) : { t: 'c', f: M + ':' + h.f, a: h.a };
    if (!b) return hh;
    const wrap = (g) => {
      g = D(g); if (g.t === 'v') return Cmp(':', [Atom(M), g]);
      const k = P.key(g); if (!k) return g;
      if (GOAL_POS[k]) { const a = g.a.slice(); for (const i of GOAL_POS[k]) a[i] = wrap(a[i]); return { t: 'c', f: g.f, a }; }
      if (k === ':/2' || B[k] || P.CONTROL.has(k)) return g;
      return Cmp(':', [Atom(M), g]);
    };
    return Cmp(':-', [hh, wrap(b)]);
  }
  const modClause = (t) => { t = D(t); if (t.t === 'c' && t.f === ':' && t.a.length === 2) { const m = D(t.a[0]); if (m.t === 'a' && !SYSMOD.has(m.n)) return intoModule(m.n, t.a[1]); return D(t.a[1]); } return t; };
  det('assert/1', (a, e) => { e.prog.add(copy(modClause(a[0]))); return true; });
  det('assertz/1', (a, e) => { e.prog.add(copy(modClause(a[0]))); return true; });
  det('asserta/1', (a, e) => { e.prog.add(copy(modClause(a[0])), null, false); return true; });
  det('$drop_module/1', (a, e) => { const pre = textOf(a[0]) + ':'; for (const k of e.prog.order) if (k.startsWith(pre)) e.prog.preds.set(k, []); return true; });
  callb('in_temporary_module/3', (a, e) => { const M = Atom('$tmp_module_' + (++e.streamSeq)); return Cmp(',', [Cmp('=', [a[0], M]), Cmp('$scc', [Atom('true'), Cmp(',', [a[1], a[2]]), Cmp('$drop_module', [M])])]); });
  det('gensym/2', (a, e) => { e.gensyms = e.gensyms || new Map(); const b = textOf(a[0]); const n = (e.gensyms.get(b) || 0) + 1; e.gensyms.set(b, n); return e.unify(a[1], Atom(b + n)); });
  det('reset_gensym/1', (a, e) => { if (e.gensyms) e.gensyms.delete(textOf(a[0])); return true; });
  det('reset_gensym/0', (a, e) => { e.gensyms = new Map(); return true; });
  // limits: a nested run with its own step budget or deadline
  function limited(e, goal, budget, onLimit) {
    const was = e.stepLimit, m = e.mark(); let ok = false;
    e.stepLimit = budget;
    try { e.solve(goal, () => { ok = true; return false; }); }
    catch (x) { e.stepLimit = was; if (x instanceof P.LimitError && x.inner) { e.undo(m); return onLimit(); } throw x; }
    e.stepLimit = was;
    if (!ok) e.undo(m);
    return ok;
  }
  // LimitError from a nested budget is marked inner, so an outer limit is not mistaken for it
  function budgetSteps(e, n) { const lim = e.steps + n, outer = e.stepLimit; return { valueOf() { if (e.steps > lim) { const x = new P.LimitError('inference limit'); x.inner = true; throw x; } return Number(outer); }, toString() { return String(outer); } }; }
  function budgetTime(e, ms) { const dl = P.now() + ms, outer = e.stepLimit; let n = 0; return { valueOf() { if ((++n & 1023) === 0 && P.now() > dl) { const x = new P.LimitError('time limit'); x.inner = true; throw x; } return Number(outer); }, toString() { return String(outer); } }; }
  det('call_with_inference_limit/3', (a, e) => {
    const n = Number(P.evalArith(a[1]).v);
    let res = Atom('!');
    const ok = limited(e, a[0], budgetSteps(e, n), () => { res = Atom('inference_limit_exceeded'); return true; });
    return ok && e.unify(a[2], res);
  });
  det('call_with_time_limit/2', (a, e) => limited(e, a[1], budgetTime(e, Number(P.evalArith(a[0]).v) * 1000), () => { throw new P.PlError(Atom('time_limit_exceeded')); }));
  det('call_with_time_limit/3', (a, e) => limited(e, a[1], budgetTime(e, Number(P.evalArith(a[0]).v) * 1000), () => { throw new P.PlError(Atom('time_limit_exceeded')); }));
  nondet('limit/2', function* (a, e) {
    const n = Number(P.evalArith(a[0]).v), sols = [];
    const tmpl = Cmp('v', P.termVars(a[1]));
    if (n > 0) { const m = e.mark(); e.solve(a[1], () => { sols.push(P.copy(P.resolve(tmpl))); return sols.length < n; }); e.undo(m); }
    for (const s1 of sols) { const m = e.mark(); if (e.unify(tmpl, s1)) yield; e.undo(m); }
  });
  det('subset/2', (a, e) => { const xs = listToArray(a[0]) || [], ys = listToArray(a[1]) || []; return xs.every((x) => ys.some((y) => { const m = e.mark(); const r = e.unify(x, y); e.undo(m); return r; })); });
  // b_setval/2: a global that backtracking restores (an entry on the trail whose undo puts the old
  // value back); the value is not copied, as in SWI-Prolog
  det('b_setval/2', (a, e) => {
    const k = textOf(a[0]), had = e.globals.has(k), old = e.globals.get(k);
    e.globals.set(k, a[1]);
    e.trail.push({ set ref(_) { if (had) e.globals.set(k, old); else e.globals.delete(k); } });
    return true;
  });
  det('b_getval/2', (a, e) => { const k = textOf(a[0]); if (!e.globals.has(k)) throw existErr('variable', a[0]); return e.unify(a[1], e.globals.get(k)); });
  // arithmetic functions as predicates (abs(X, Y) is Y is abs(X)), as SWI-Prolog 9 has them
  for (const [f, n] of [['abs', 1], ['sign', 1], ['trunc', 1], ['max', 2], ['min', 2], ['truncate', 1], ['ceiling', 1], ['floor', 1], ['round', 1], ['sqrt', 1], ['sin', 1], ['cos', 1], ['tan', 1], ['asin', 1], ['acos', 1], ['atan', 1], ['log', 1], ['exp', 1], ['gcd', 2], ['msb', 1]]) if (!B[f + '/' + (n + 1)]) det(f + '/' + (n + 1), (a, e) => e.unify(a[n], P.evalArith(Cmp(f, a.slice(0, n)))));
  det('safe_goal/1', () => true); // library(sandbox): the interpreter runs programs in its own engine
  det('findnsols/4', (a, e) => {
    const n = Number(P.evalArith(a[0]).v), out = [];
    const m = e.mark();
    if (n > 0) e.solve(a[2], () => { out.push(P.copy(P.resolve(a[1]))); return out.length < n; });
    e.undo(m);
    return e.unify(a[3], list(out));
  });
  det('findnsols/5', (a, e) => {
    const n = Number(P.evalArith(a[0]).v), out = [];
    const m = e.mark();
    if (n > 0) e.solve(a[2], () => { out.push(P.copy(P.resolve(a[1]))); return out.length < n; });
    e.undo(m);
    return e.unify(a[3], list(out, a[4]));
  });
  det('term_hash/2', (a, e) => { if (!isGround(a[0])) return true; let h = 0; const s = show(a[0], { quoted: true }); for (let i = 0; i < s.length; i++) h = (h * 31 + s.charCodeAt(i)) & 0xffffff; return e.unify(a[1], Int(h)); });
  det('tab/1', (a, e) => { e.write(' '.repeat(Number(P.evalArith(a[0]).v))); return true; });

  // Library predicates written in Prolog, added to every program the interpreter runs (so the
  // converter sees them as ordinary predicates). setup_call_cleanup keeps the goal's first answer.
  P.SWI_PRELUDE = `
'$scc'(S, G, C) :- once(S), catch(G, E, true) -> ignore(C), ( var(E) -> true ; throw(E) ) ; ignore(C), fail.
convlist(_, [], []).
convlist(G, [X|Xs], Ys) :- ( call(G, X, Y) -> Ys = [Y|Ys1] ; Ys = Ys1 ), convlist(G, Xs, Ys1).
assertion(G) :- ( \\+ \\+ G -> true ; throw(error(assertion_failed(G), _)) ).
must_be(Type, X) :- '$must_be'(Type, X).
'$must_be'(_, X) :- var(X), !, throw(error(instantiation_error, _)).
'$must_be'(list, X) :- !, ( is_list(X) -> true ; throw(error(type_error(list, X), _)) ).
'$must_be'(integer, X) :- !, ( integer(X) -> true ; throw(error(type_error(integer, X), _)) ).
'$must_be'(atom, X) :- !, ( atom(X) -> true ; throw(error(type_error(atom, X), _)) ).
'$must_be'(callable, X) :- !, ( callable(X) -> true ; throw(error(type_error(callable, X), _)) ).
'$must_be'(boolean, X) :- !, ( (X == true ; X == false) -> true ; throw(error(type_error(boolean, X), _)) ).
'$must_be'(nonneg, X) :- !, ( integer(X), X >= 0 -> true ; throw(error(type_error(nonneg, X), _)) ).
'$must_be'(positive_integer, X) :- !, ( integer(X), X > 0 -> true ; throw(error(type_error(positive_integer, X), _)) ).
'$must_be'(_, _).
is_of_type(Type, X) :- catch('$must_be'(Type, X), _, fail).
max_member(P, M, L) :- L = [H|T], foldl([X, A0, A]>>( call(P, A0, X) -> A = X ; A = A0 ), T, H, M).
nb_increment(K) :- nb_getval(K, V), V1 is V + 1, nb_setval(K, V1).
option(Opt, Options, Default) :- arg(1, Opt, V), functor(Opt, N, 1), functor(G, N, 1), ( memberchk(G, Options) -> arg(1, G, V) ; memberchk(N = V0, Options) -> V = V0 ; V = Default ).
option(Opt, Options) :- functor(Opt, N, 1), arg(1, Opt, V), ( memberchk(Opt, Options) -> true ; memberchk(N = V, Options) ).
select_option(Opt, Options, Rest) :- functor(Opt, N, 1), functor(G, N, 1), select(G, Options, Rest), !, Opt = G.
select_option(Opt, Options, Rest, Default) :- ( select_option(Opt, Options, Rest) -> true ; arg(1, Opt, Default), Rest = Options ).
selectchk(X, Xs, Y, Ys) :- '$select4'(X, Xs, Y, Ys), !.
'$select4'(X, [X|T], Y, [Y|T]).
'$select4'(X, [H|T], Y, [H|T2]) :- '$select4'(X, T, Y, T2).
select(X, Xs, Y, Ys) :- '$select4'(X, Xs, Y, Ys).
same_length([], []).
same_length([_|A], [_|B]) :- same_length(A, B).
map_list_to_pairs(F, L, Ps) :- '$mltp'(L, F, Ps).
'$mltp'([], _, []).
'$mltp'([H|T], F, [K-H|Ps]) :- call(F, H, K), '$mltp'(T, F, Ps).
nth0(I, L, E, R) :- integer(I), !, I >= 0, '$nth_del'(I, L, E, R).
nth0(I, L, E, R) :- var(I), '$nth_gen'(L, E, R, 0, I).
nth1(I, L, E, R) :- integer(I), !, I0 is I - 1, nth0(I0, L, E, R).
nth1(I, L, E, R) :- nth0(I0, L, E, R), I is I0 + 1.
'$nth_del'(0, [E|R], E, R) :- !.
'$nth_del'(I, [H|T], E, [H|R]) :- I1 is I - 1, '$nth_del'(I1, T, E, R).
'$nth_gen'([E|R], E, R, B, B).
'$nth_gen'([H|T], E, [H|R], B0, B) :- B1 is B0 + 1, '$nth_gen'(T, E, R, B1, B).
empty_assoc('$assoc'([])).
get_assoc(K, '$assoc'(L), V) :- '$get_assoc'(L, K, V).
'$get_assoc'([K0-V0|T], K, V) :- compare(O, K, K0), ( O = (=) -> V = V0 ; O = (>) -> '$get_assoc'(T, K, V) ).
put_assoc(K, '$assoc'(L), V, '$assoc'(L2)) :- '$put_assoc'(L, K, V, L2).
'$put_assoc'([], K, V, [K-V]).
'$put_assoc'([K0-V0|T], K, V, L) :- compare(O, K, K0), ( O = (=) -> L = [K-V|T] ; O = (<) -> L = [K-V, K0-V0|T] ; L = [K0-V0|L1], '$put_assoc'(T, K, V, L1) ).
list_to_assoc(Ps, '$assoc'(L)) :- keysort(Ps, L).
assoc_to_list('$assoc'(L), L).
assoc_to_keys('$assoc'(L), Ks) :- pairs_keys(L, Ks).
assoc_to_values('$assoc'(L), Vs) :- pairs_values(L, Vs).
max_assoc('$assoc'(L), K, V) :- last(L, K-V).
min_assoc('$assoc'([K-V|_]), K, V).
del_assoc(K, '$assoc'(L), V, '$assoc'(L2)) :- select(K0-V, L, L2), K0 == K, !.
% plunit: the loader keeps test(Name[, Options]) :- Body between begin_tests/end_tests as '$plunit_test'/4
:- dynamic('$plunit_test'/4).
:- dynamic('$plunit_unit'/2).
begin_tests(_).
begin_tests(_, _).
end_tests(_).
run_tests :- '$run_tests'(_).
run_tests(Spec) :- is_list(Spec), !, forall(member(S, Spec), run_tests(S)).
run_tests(Spec) :- ( Spec = U:N -> true ; U = Spec ), '$run_tests'(U, N).
'$run_tests'(U) :- '$run_tests'(U, _).
'$run_tests'(U, N) :-
    findall(U-N-O-I, ( clause('$plunit_test'(U, N, O, I), _), \\+ ( '$plunit_unit'(U, UO), '$unit_skip'(UO) ) ), Ts),
    foldl('$run_test', Ts, 0-0, Pass-Fail),
    Total is Pass + Fail,
    ( Fail =:= 0 -> format(user_error, "% All ~w tests passed~n", [Total]) ; format(user_error, "% ~w tests failed~n% ~w tests passed~n", [Fail, Pass]), fail ).
'$run_test'(U-N-O0-I, P0-F0, P-F) :-
    ( is_list(O0) -> O = O0 ; O = [O0] ),
    ( ( memberchk(blocked(_), O) ; memberchk(fixme(_), O) ; memberchk(condition(C), O), \+ catch(C, _, fail) ) -> P = P0, F = F0
    ; ( memberchk(setup(S), O) -> catch(S, _, true) ; true ),
      ( catch('$test_ok'(U, N, O, I), E, ( format(user_error, "ERROR: test ~w:~w: caught exception ~q~n", [U, N, E]), fail ))
      -> P is P0 + 1, F = F0
      ;  F is F0 + 1, P = P0, format(user_error, "ERROR: test ~w:~w: failed~n", [U, N]) ),
      ( memberchk(cleanup(Cl), O) -> catch(Cl, _, true) ; true ) ).
'$test_ok'(U, N, O, I) :-
    ( memberchk(fail, O) -> \\+ '$plunit_test'(U, N, _, I)
    ; memberchk(false, O) -> \\+ '$plunit_test'(U, N, _, I)
    ; memberchk(throws(E), O) -> catch(('$plunit_test'(U, N, _, I), fail), X, subsumes_term(E, X))
    ; memberchk(error(E), O) -> catch(('$plunit_test'(U, N, _, I), fail), X, subsumes_term(error(E, _), X))
    ; memberchk(all(Cmp), O) -> Cmp =.. [Op, _, L], findall(T, ( '$plunit_test'(U, N, O1, I), '$opts'(O1, Os1), memberchk(all(C1), Os1), arg(1, C1, T) ), L1), call(Op, L1, L)
    ; memberchk(set(Cmp), O) -> Cmp =.. [Op, _, L], findall(T, ( '$plunit_test'(U, N, O1, I), '$opts'(O1, Os1), memberchk(set(C1), Os1), arg(1, C1, T) ), L0), sort(L0, L1), sort(L, L2), call(Op, L1, L2)
    ; once('$plunit_test'(U, N, O2, I)), '$opts'(O2, Os2), forall(( member(C, Os2), '$test_cond'(C, G) ), G) ).
'$unit_skip'(UO) :- '$opts'(UO, Os), ( memberchk(blocked(_), Os) ; memberchk(condition(C), Os), \\+ catch(C, _, fail) ), !.
'$opts'(O, Os) :- ( is_list(O) -> Os = O ; Os = [O] ).
'$test_cond'(true(G), G) :- !.
'$test_cond'(C, C) :- compound(C), functor(C, F, 2), memberchk(F, [==, =, =:=, =@=, \\==, \\=]).
random_permutation(L, P) :- is_list(L), !, findall(K-X, (member(X, L), random(K)), KXs), keysort(KXs, S), pairs_values(S, P).
random_permutation(L, P) :- random_permutation(P, L).
random_member(X, L) :- length(L, N), N > 0, I is random(N), nth0(I, L, X).
random_select(X, L, R) :- length(L, N), N > 0, I is random(N), nth0(I, L, X, R).
list_to_ord_set(L, S) :- sort(L, S).
ord_union(A, B, C) :- append(A, B, L), sort(L, C).
ord_union(Ls, S) :- append(Ls, L), sort(L, S).
ord_subtract(A, B, C) :- exclude([X]>>ord_memberchk(X, B), A, C).
ord_intersection(A, B, C) :- include([X]>>ord_memberchk(X, B), A, C).
ord_memberchk(X, L) :- memberchk(X, L).
ord_subset(A, B) :- forall(member(X, A), ord_memberchk(X, B)).
ord_insert(S, E, S2) :- ord_union(S, [E], S2).
ord_add_element(S, E, S2) :- ord_union(S, [E], S2).
ord_del_element(S, E, S2) :- ord_subtract(S, [E], S2).
ord_empty([]).
sumlist(L, S) :- sum_list(L, S).
partition(P, L, I, E, G) :- '$partition5'(L, P, I, E, G).
'$partition5'([], _, [], [], []).
'$partition5'([H|T], P, I, E, G) :- call(P, O, H), '$partition5_'(O, H, P, T, I, E, G).
'$partition5_'(<, H, P, T, [H|I], E, G) :- '$partition5'(T, P, I, E, G).
'$partition5_'(=, H, P, T, I, [H|E], G) :- '$partition5'(T, P, I, E, G).
'$partition5_'(>, H, P, T, I, E, [H|G]) :- '$partition5'(T, P, I, E, G).
subsumes_term(G, S) :- \\+ \\+ ( term_variables(S, V1), G = S, term_variables(V1, V2), V1 == V2 ).
`;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
