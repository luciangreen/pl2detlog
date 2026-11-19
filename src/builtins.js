/* pl2detlog builtins for the reference engine. det: fn(args, eng) -> bool.
   nondet: generator fn yielding once per solution (bindings made before yield). */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show, evalArith, textOf, parseNumber, charsList, codesList, typeError, instErr, PlError, sortUnique } = P;
  const B = {};
  const det = (k, fn) => { B[k] = { fn }; };
  const nondet = (k, fn) => { B[k] = { fn, nondet: true }; };
  const callb = (k, fn) => { B[k] = { fn, call: true }; };
  const D = deref;
  const arr = (t) => { const a = listToArray(t); if (!a) { if (D(t).t === 'v') throw instErr(); throw typeError('list', t); } return a; };
  const add = (x, k) => evalArith(Cmp('+', [x, Int(k)]));
  const numCmp = (a, b) => { const x = evalArith(a), y = evalArith(b); return x.v < y.v ? -1 : x.v > y.v ? 1 : 0; };

  // type checks
  det('var/1', a => D(a[0]).t === 'v');
  det('nonvar/1', a => D(a[0]).t !== 'v');
  det('atom/1', a => D(a[0]).t === 'a');
  det('number/1', a => D(a[0]).t === 'n');
  det('integer/1', a => { const x = D(a[0]); return x.t === 'n' && !x.f; });
  det('float/1', a => { const x = D(a[0]); return x.t === 'n' && x.f; });
  det('atomic/1', a => { const x = D(a[0]); return x.t === 'a' || x.t === 'n' || x.t === 's'; });
  det('compound/1', a => D(a[0]).t === 'c');
  det('callable/1', a => { const x = D(a[0]); return x.t === 'a' || x.t === 'c'; });
  det('is_list/1', a => listToArray(a[0]) !== null);
  det('string/1', a => D(a[0]).t === 's');
  det('ground/1', a => isGround(a[0]));
  det('is_dict/1', () => false);
  det('is_assoc/1', () => false);

  // unification / comparison
  det('=/2', (a, e) => e.unify(a[0], a[1]));
  det('\\=/2', (a, e) => { const m = e.trail.length; const r = e.unify(a[0], a[1]); e.undo(m); return !r; });
  det('unify_with_occurs_check/2', (a, e) => e.unify(a[0], a[1]));
  det('==/2', a => compare(a[0], a[1]) === 0);
  det('\\==/2', a => compare(a[0], a[1]) !== 0);
  det('@</2', a => compare(a[0], a[1]) < 0);
  det('@>/2', a => compare(a[0], a[1]) > 0);
  det('@=</2', a => compare(a[0], a[1]) <= 0);
  det('@>=/2', a => compare(a[0], a[1]) >= 0);
  det('compare/3', (a, e) => { const c = compare(a[1], a[2]); return e.unify(a[0], Atom(c < 0 ? '<' : c > 0 ? '>' : '=')); });
  det('is/2', (a, e) => e.unify(a[0], evalArith(a[1])));
  det('=:=/2', a => numCmp(a[0], a[1]) === 0);
  det('=\\=/2', a => numCmp(a[0], a[1]) !== 0);
  det('</2', a => numCmp(a[0], a[1]) < 0);
  det('>/2', a => numCmp(a[0], a[1]) > 0);
  det('=</2', a => numCmp(a[0], a[1]) <= 0);
  det('>=/2', a => numCmp(a[0], a[1]) >= 0);
  det('succ/2', (a, e) => { const x = D(a[0]); if (x.t === 'n') return e.unify(a[1], add(x, 1)); const y = D(a[1]); if (y.t === 'v') throw instErr(); if (y.v <= 0) return false; return e.unify(a[0], add(y, -1)); });
  det('plus/3', (a, e) => { const x = D(a[0]), y = D(a[1]), z = D(a[2]); const ar = (f, p, q) => evalArith(Cmp(f, [p, q])); if (x.t === 'n' && y.t === 'n') return e.unify(z, ar('+', x, y)); if (x.t === 'n' && z.t === 'n') return e.unify(y, ar('-', z, x)); if (y.t === 'n' && z.t === 'n') return e.unify(x, ar('-', z, y)); throw instErr(); });

  // terms
  det('functor/3', (a, e) => {
    const t = D(a[0]);
    if (t.t === 'v') { const n = D(a[2]).v; const nm = D(a[1]); if (n === 0) return e.unify(t, nm); const args = []; for (let i = 0; i < n; i++) args.push(Var()); return e.unify(t, Cmp(nm.n, args)); }
    if (t.t === 'c') return e.unify(a[1], Atom(t.f)) && e.unify(a[2], Int(t.a.length));
    return e.unify(a[1], t) && e.unify(a[2], Int(0));
  });
  nondet('arg/3', function* (a, e) {
    const n = D(a[0]), t = D(a[1]);
    if (t.t !== 'c') throw typeError('compound', t);
    if (n.t === 'n') { if (n.v >= 1 && n.v <= t.a.length && e.unify(a[2], t.a[n.v - 1])) yield 'last'; return; }
    for (let i = 0; i < t.a.length; i++) { const m = e.trail.length; if (e.unify(n, Int(i + 1)) && e.unify(a[2], t.a[i])) yield; e.undo(m); }
  });
  det('=../2', (a, e) => {
    const t = D(a[0]);
    if (t.t === 'c') return e.unify(a[1], list([Atom(t.f)].concat(t.a)));
    if (t.t !== 'v') return e.unify(a[1], list([t]));
    const l = arr(a[1]); const h = D(l[0]);
    if (l.length === 1) return e.unify(t, h);
    return e.unify(t, Cmp(h.n, l.slice(1)));
  });
  det('copy_term/2', (a, e) => e.unify(a[1], copy(a[0])));
  det('numbervars/3', (a, e) => { let n = D(a[1]).v; for (const v of termVars(a[0])) e.bind(v, Cmp('$VAR', [Int(n++)])); return e.unify(a[2], Int(n)); });
  det('term_variables/2', (a, e) => e.unify(a[1], list(termVars(a[0]))));
  det('setarg/3', (a) => { const t = D(a[1]); t.a[D(a[0]).v - 1] = copy(a[2]); return true; });
  det('nb_setarg/3', (a) => { const t = D(a[1]); t.a[D(a[0]).v - 1] = copy(a[2]); return true; });
  det('term_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(show(t))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('term_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(show(t))); return e.unify(t, P.readTerm(textOf(a[1])).term); });
  det('read_term_from_atom/3', (a, e) => e.unify(a[1], P.readTerm(textOf(a[0])).term));
  det('tab/1', (a, e) => { e.write(' '.repeat(evalArith(a[0]).v)); return true; });

  // output
  det('write/1', (a, e) => { e.write(show(a[0], { quoted: false })); return true; });
  det('print/1', (a, e) => { e.write(show(a[0], { quoted: true })); return true; });
  det('writeln/1', (a, e) => { e.write(show(a[0], { quoted: false }) + '\n'); return true; });
  det('writeq/1', (a, e) => { e.write(show(a[0], { quoted: true })); return true; });
  det('write_canonical/1', (a, e) => { e.write(show(a[0], { quoted: true, ignoreOps: true })); return true; });
  det('write_term/2', (a, e) => { e.write(show(a[0], { quoted: false })); return true; });
  det('nl/0', (a, e) => { e.write('\n'); return true; });
  det('put_char/1', (a, e) => { e.write(D(a[0]).n); return true; });
  det('format/1', (a, e) => { e.write(P.format(a[0], NIL)); return true; });
  det('format/2', (a, e) => { e.write(P.format(a[0], a[1])); return true; });
  det('format/3', (a, e) => {
    const s = D(a[0]); const txt = P.format(a[1], a[2]);
    if (s.t === 'c' && s.a.length === 1) {
      const k = s.f; const v = k === 'atom' ? Atom(txt) : k === 'string' ? Str(txt) : k === 'codes' ? codesList(txt) : k === 'chars' ? charsList(txt) : null;
      if (v) return e.unify(s.a[0], v);
    }
    e.write(txt); return true;
  });
  det('flush_output/0', () => true);
  // halt is not an error: no catch/3 sees it; the run stops with its exit code
  det('halt/0', () => { throw { halt: true, code: 0 }; });
  det('halt/1', (a) => { const c = evalArith(a[0]); throw { halt: true, code: Number(c.v) }; });

  // atoms & strings
  det('atom_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(textOf(t))); return e.unify(t, Atom(textOf(a[1]))); });
  det('atom_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(textOf(t))); return e.unify(t, Atom(textOf(a[1]))); });
  det('char_code/2', (a, e) => { const t = D(a[0]); if (t.t === 'a') return e.unify(a[1], Int(t.n.codePointAt(0))); return e.unify(t, Atom(String.fromCodePoint(D(a[1]).v))); });
  det('atom_length/2', (a, e) => e.unify(a[1], Int([...textOf(a[0])].length)));
  det('string_length/2', (a, e) => e.unify(a[1], Int([...textOf(a[0])].length)));
  det('atom_number/2', (a, e) => { const t = D(a[0]); if (t.t === 'v') { const n = D(a[1]); if (n.t === 'v') throw instErr(); return e.unify(t, Atom(show(n))); } const n = parseNumber(textOf(t)); return n ? e.unify(a[1], n) : false; });
  det('number_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(show(t))); const n = parseNumber(textOf(a[1])); if (!n) throw new PlError(Cmp('error', [Cmp('syntax_error', [Atom('illegal_number')]), Var()])); return e.unify(t, n); });
  det('number_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(show(t))); const n = parseNumber(textOf(a[1])); if (!n) throw new PlError(Cmp('error', [Cmp('syntax_error', [Atom('illegal_number')]), Var()])); return e.unify(t, n); });
  det('number_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(show(t))); const n = parseNumber(textOf(a[1])); return n ? e.unify(t, n) : false; });
  det('atom_string/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Str(textOf(t))); return e.unify(t, Atom(textOf(a[1]))); });
  det('number_vars/3', () => true);
  det('string_chars/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], charsList(textOf(t))); return e.unify(t, Str(textOf(a[1]))); });
  det('string_codes/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], codesList(textOf(t))); return e.unify(t, Str(textOf(a[1]))); });
  det('string_to_atom/2', (a, e) => { const t = D(a[0]); if (t.t !== 'v') return e.unify(a[1], Atom(textOf(t))); return e.unify(t, Str(textOf(a[1]))); });
  det('string_code/3', (a, e) => { const s = [...textOf(a[1])]; const i = D(a[0]).v; if (i < 1 || i > s.length) return false; return e.unify(a[2], Int(s[i - 1].codePointAt(0))); });
  det('number_codes/2', B['number_codes/2'].fn);
  det('string/1', a => D(a[0]).t === 's');
  det('text_concat/3', (a, e) => e.unify(a[2], Atom(textOf(a[0]) + textOf(a[1]))));
  det('string_number/2', (a, e) => { const n = parseNumber(textOf(a[0])); return n ? e.unify(a[1], n) : false; });
  det('term_string/3', B['term_string/2'].fn);
  det('upcase_atom/2', (a, e) => e.unify(a[1], Atom(textOf(a[0]).toUpperCase())));
  det('downcase_atom/2', (a, e) => e.unify(a[1], Atom(textOf(a[0]).toLowerCase())));
  det('string_upper/2', (a, e) => e.unify(a[1], Str(textOf(a[0]).toUpperCase())));
  det('string_lower/2', (a, e) => e.unify(a[1], Str(textOf(a[0]).toLowerCase())));
  det('normalize_space/2', (a, e) => { const s = textOf(a[1]).trim().split(/\s+/).join(' '); const sp = D(a[0]); const k = sp.f; return e.unify(sp.a[0], k === 'atom' ? Atom(s) : k === 'string' ? Str(s) : k === 'codes' ? codesList(s) : charsList(s)); });
  det('split_string/4', (a, e) => {
    const s = textOf(a[0]), sep = textOf(a[1]), pad = textOf(a[2]);
    const parts = []; let cur = '';
    if (sep.length === 0) parts.push(s); else { for (const c of s) { if (sep.includes(c)) { parts.push(cur); cur = ''; } else cur += c; } parts.push(cur); }
    const strip = x => { let i = 0, j = x.length; while (i < j && pad.includes(x[i])) i++; while (j > i && pad.includes(x[j - 1])) j--; return x.slice(i, j); };
    return e.unify(a[3], list(parts.map(p => Str(strip(p)))));
  });
  det('atomic_list_concat/2', (a, e) => e.unify(a[1], Atom(arr(a[0]).map(x => textOf(x)).join(''))));
  det('atomic_list_concat/3', (a, e) => {
    const sep = textOf(a[1]); const l = listToArray(a[0]);
    if (l && l.every(x => D(x).t !== 'v')) return e.unify(a[2], Atom(l.map(x => textOf(x)).join(sep)));
    if (sep === '') throw instErr();
    return e.unify(a[0], list(textOf(a[2]).split(sep).map(x => Atom(x))));
  });
  nondet('string_concat/3', function* (a, e) {
    const x = D(a[0]), y = D(a[1]);
    if (x.t !== 'v' && y.t !== 'v') { if (e.unify(a[2], Str(textOf(x) + textOf(y)))) yield 'last'; return; }
    const z = textOf(a[2]);
    if (x.t !== 'v') { const p = textOf(x); if (z.startsWith(p) && e.unify(y, Str(z.slice(p.length)))) yield 'last'; return; }
    if (y.t !== 'v') { const q = textOf(y); if (z.endsWith(q) && e.unify(x, Str(z.slice(0, z.length - q.length)))) yield 'last'; return; }
    const cs = [...z];
    for (let i = 0; i <= cs.length; i++) { const m = e.trail.length; if (e.unify(x, Str(cs.slice(0, i).join(''))) && e.unify(y, Str(cs.slice(i).join('')))) yield; e.undo(m); }
  });
  nondet('atom_concat/3', function* (a, e) {
    const x = D(a[0]), y = D(a[1]);
    if (x.t !== 'v' && y.t !== 'v') { if (e.unify(a[2], Atom(textOf(x) + textOf(y)))) yield 'last'; return; }
    const z = [...textOf(a[2])];
    for (let i = 0; i <= z.length; i++) { const m = e.trail.length; if (e.unify(x, Atom(z.slice(0, i).join(''))) && e.unify(y, Atom(z.slice(i).join('')))) yield; e.undo(m); }
  });
  function* subText(a, e, mk) {
    const s = [...textOf(a[0])]; const n = s.length;
    const Bf = D(a[1]), L = D(a[2]), Af = D(a[3]), Sub = D(a[4]);
    if (Sub.t !== 'v') {
      const sub = [...textOf(Sub)]; const k = sub.length; const subs = sub.join('');
      for (let i = 0; i + k <= n; i++) if (s.slice(i, i + k).join('') === subs) { const m = e.trail.length; if (e.unify(Bf, Int(i)) && e.unify(L, Int(k)) && e.unify(Af, Int(n - i - k))) yield; e.undo(m); }
      return;
    }
    for (let i = 0; i <= n; i++) {
      if (Bf.t === 'n' && Bf.v !== i) continue;
      for (let k = 0; i + k <= n; k++) {
        if (L.t === 'n' && L.v !== k) continue;
        if (Af.t === 'n' && Af.v !== n - i - k) continue;
        const m = e.trail.length;
        if (e.unify(Bf, Int(i)) && e.unify(L, Int(k)) && e.unify(Af, Int(n - i - k)) && e.unify(Sub, mk(s.slice(i, i + k).join('')))) yield;
        e.undo(m);
      }
    }
  }
  nondet('sub_atom/5', function* (a, e) { yield* subText(a, e, Atom); });
  nondet('sub_string/5', function* (a, e) { yield* subText(a, e, Str); });
  nondet('char_type/2', function* (a, e) {
    const c = D(a[0]); const ty = D(a[1]);
    if (c.t === 'v') throw instErr();
    const ch = c.t === 'n' ? String.fromCodePoint(c.v) : c.n;
    const tn = ty.t === 'a' ? ty.n : ty.f;
    let ok = null;
    switch (tn) {
      case 'alpha': ok = /[\p{L}\p{N}_]/u.test(ch); break;
      case 'alnum': ok = /[\p{L}\p{N}]/u.test(ch); break;
      case 'digit': if (ty.t === 'c') { if (/[0-9]/.test(ch)) { if (e.unify(ty.a[0], Int(+ch))) yield 'last'; } return; } ok = /[0-9]/.test(ch); break;
      case 'space': case 'white': ok = /\s/.test(ch); break;
      case 'upper': if (ty.t === 'c') { if (ch !== ch.toLowerCase() || /[A-Z]/.test(ch)) { if (e.unify(ty.a[0], Atom(ch.toLowerCase()))) yield 'last'; } return; } ok = /\p{Lu}/u.test(ch); break;
      case 'lower': if (ty.t === 'c') { if (/\p{Ll}/u.test(ch)) { if (e.unify(ty.a[0], Atom(ch.toUpperCase()))) yield 'last'; } return; } ok = /\p{Ll}/u.test(ch); break;
      case 'punct': ok = /[!-\/:-@\[-`{-~]/.test(ch); break;
      case 'csym': ok = /[A-Za-z0-9_]/.test(ch); break;
      case 'csymf': ok = /[A-Za-z_]/.test(ch); break;
      case 'end_of_line': ok = /[\n\r]/.test(ch); break;
      case 'graph': ok = /[!-~]/.test(ch) && !/[A-Za-z0-9]/.test(ch); break;
      case 'to_lower': if (e.unify(ty.a[0], Atom(ch.toLowerCase()))) yield 'last'; return;
      case 'to_upper': if (e.unify(ty.a[0], Atom(ch.toUpperCase()))) yield 'last'; return;
    }
    if (ok) yield 'last';
  });
  det('code_type/2', (a, e) => { const c = D(a[0]); const ch = c.t === 'n' ? String.fromCodePoint(c.v) : c.n; const ty = P.name(a[1]); if (ty === 'digit' && D(a[1]).t === 'c') return /[0-9]/.test(ch) && e.unify(D(a[1]).a[0], Int(+ch)); const re = { alpha: /[A-Za-z0-9_]/, alnum: /[A-Za-z0-9]/, digit: /[0-9]/, space: /\s/, white: /[ \t]/, upper: /[A-Z]/, lower: /[a-z]/, punct: /[!-\/:-@\[-`{-~]/, csym: /[A-Za-z0-9_]/, csymf: /[A-Za-z_]/ }[ty]; return re ? re.test(ch) : false; });

  // lists
  nondet('between/3', function* (a, e) {
    const lo = evalArith(a[0]).v, hiT = D(a[1]); const hi = hiT.t === 'a' && (hiT.n === 'inf' || hiT.n === 'infinite') ? Infinity : evalArith(hiT).v;
    const x = D(a[2]);
    if (x.t === 'n') { if (x.v >= lo && x.v <= hi) yield 'last'; return; }
    for (let i = lo; i <= hi; i++) { const m = e.trail.length; if (e.unify(x, Int(i))) yield i === hi ? 'last' : undefined; e.undo(m); }
  });
  nondet('member/2', function* (a, e) {
    let l = D(a[1]);
    while (isCons(l)) {
      const nx = D(l.a[1]);
      const m = e.trail.length;
      if (e.unify(a[0], l.a[0])) yield (isNil(nx) ? 'last' : undefined);
      e.undo(m);
      l = nx;
    }
    if (l.t === 'v') { // partial list: generate
      for (;;) { const h = Var(), t = Var(); const m = e.trail.length; e.bind(l, cons(h, t)); if (e.unify(a[0], h)) yield; e.undo(m); const h2 = Var(); e.bind(l, cons(h2, t)); l = t; }
    }
  });
  det('memberchk/2', (a, e) => { let l = D(a[1]); while (isCons(l)) { const m = e.trail.length; if (e.unify(a[0], l.a[0])) return true; e.undo(m); l = D(l.a[1]); } if (l.t === 'v') { return e.unify(l, cons(a[0], Var())); } return false; });
  nondet('append/3', function* (a, e) {
    const xs = listToArray(a[0]);
    if (xs) { if (e.unify(a[2], list(xs, a[1]))) yield 'last'; return; }
    { let x = D(a[0]); while (isCons(x)) x = D(x.a[1]); if (x.t !== 'v' && !P.isNil(x)) return; } // not a (partial) list
    { let z = D(a[2]); while (isCons(z)) z = D(z.a[1]); if (z.t !== 'v' && !P.isNil(z)) return; }
    // enumerate prefixes of a[2]
    let z = D(a[2]); const pre = [];
    for (;;) {
      const m = e.trail.length;
      if (e.unify(a[0], list(pre)) && e.unify(a[1], z)) yield (isNil(z) ? 'last' : undefined);
      e.undo(m);
      if (isCons(z)) { pre.push(z.a[0]); z = D(z.a[1]); continue; }
      if (z.t === 'v') { const h = Var(), t = Var(); e.bind(z, cons(h, t)); pre.push(h); z = t; continue; }
      return;
    }
  });
  det('append/2', (a, e) => { const ls = arr(a[0]); let r = NIL; const parts = ls.map(arr); const all = [].concat(...parts); return e.unify(a[1], list(all)); });
  nondet('length/2', function* (a, e) {
    let l = D(a[0]); let n = 0;
    while (isCons(l)) { n++; l = D(l.a[1]); }
    if (isNil(l)) { if (e.unify(a[1], Int(n))) yield 'last'; return; }
    if (l.t !== 'v') return;
    const N = D(a[1]);
    if (N.t === 'n') { if (N.v < n) return; const vs = []; for (let i = n; i < N.v; i++) vs.push(Var()); if (e.unify(l, list(vs))) yield 'last'; return; }
    for (let k = n; ; k++) { const vs = []; for (let i = n; i < k; i++) vs.push(Var()); const m = e.trail.length; if (e.unify(l, list(vs)) && e.unify(N, Int(k))) yield; e.undo(m); }
  });
  det('reverse/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().reverse())));
  nondet('nth0/3', function* (a, e) { yield* nth(a, e, 0); });
  nondet('nth1/3', function* (a, e) { yield* nth(a, e, 1); });
  function* nth(a, e, base) {
    const i = D(a[0]); const l = arr(a[1]);
    if (i.t === 'n') { if (typeof i.v !== 'number') return; const k = i.v - base; if (k >= 0 && k < l.length && e.unify(a[2], l[k])) yield 'last'; return; }
    for (let k = 0; k < l.length; k++) { const m = e.trail.length; if (e.unify(i, Int(k + base)) && e.unify(a[2], l[k])) yield; e.undo(m); }
  }
  nondet('last/2', function* (a, e) { const l = arr(a[0]); if (l.length && e.unify(a[1], l[l.length - 1])) yield 'last'; });
  det('msort/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().sort(compare))));
  det('sort/2', (a, e) => e.unify(a[1], list(sortUnique(arr(a[0])))));
  det('predsort/3', () => { throw new Error('predsort/3 is not supported'); });
  det('sort/4', (a, e) => {
    const k = D(a[0]).v; const ord = D(a[1]).n; let l = arr(a[2]).slice();
    const kf = x => k === 0 ? x : D(x).a[k - 1];
    const cmp = (x, y) => compare(kf(x), kf(y));
    if (ord === '@<' || ord === '@=<') l.sort(cmp); else l.sort((x, y) => -cmp(x, y));
    if (ord === '@<' || ord === '@>') { const o = []; for (const x of l) if (!o.length || cmp(o[o.length - 1], x) !== 0) o.push(x); l = o; }
    return e.unify(a[3], list(l));
  });
  det('keysort/2', (a, e) => e.unify(a[1], list(arr(a[0]).slice().sort((x, y) => compare(D(x).a[0], D(y).a[0])))));
  det('list_to_set/2', (a, e) => { const o = []; for (const x of arr(a[0])) if (!o.some(y => compare(x, y) === 0)) o.push(x); return e.unify(a[1], list(o)); });
  det('sum_list/2', (a, e) => { let s = Int(0); for (const x of arr(a[0])) s = evalArith(Cmp('+', [s, x])); return e.unify(a[1], s); });
  det('sumlist/2', B['sum_list/2'].fn);
  det('max_list/2', (a, e) => { const l = arr(a[0]).map(evalArith); if (!l.length) return false; return e.unify(a[1], l.reduce((m, x) => x.v > m.v ? x : m)); });
  det('min_list/2', (a, e) => { const l = arr(a[0]).map(evalArith); if (!l.length) return false; return e.unify(a[1], l.reduce((m, x) => x.v < m.v ? x : m)); });
  det('max_member/2', (a, e) => { const l = arr(a[1]); if (!l.length) return false; return e.unify(a[0], l.reduce((m, x) => compare(x, m) > 0 ? x : m)); });
  det('min_member/2', (a, e) => { const l = arr(a[1]); if (!l.length) return false; return e.unify(a[0], l.reduce((m, x) => compare(x, m) < 0 ? x : m)); });
  // the list is ground: its cells are marked so (copies and groundness checks of it are then O(1))
  det('numlist/3', (a, e) => { const lo = evalArith(a[0]).v, hi = evalArith(a[1]).v; let l = P.NIL; for (let i = hi; i >= lo; i--) l = { t: 'c', f: '.', a: [Int(i), l], gr: true }; return e.unify(a[2], l); });
  det('delete/3', (a, e) => { const o = arr(a[0]).filter(x => { const m = e.trail.length; const r = e.unify(x, a[1]); e.undo(m); return !r; }); return e.unify(a[2], list(o)); });
  det('exclude_eq/3', () => false);
  det('subtract/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => !b.some(y => { const m = e.trail.length; const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o)); });
  det('intersection/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => b.some(y => { const m = e.trail.length; const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o)); });
  det('union/3', (a, e) => { const b = arr(a[1]); const o = arr(a[0]).filter(x => !b.some(y => { const m = e.trail.length; const r = e.unify(x, y); e.undo(m); return r; })); return e.unify(a[2], list(o.concat(b))); });
  det('flatten/2', (a, e) => { const o = []; (function f(t) { t = D(t); if (isNil(t)) return; if (isCons(t)) { f(t.a[0]); f(t.a[1]); return; } o.push(t); })(a[0]); return e.unify(a[1], list(o)); });
  det('sumlist/3', () => false);
  det('exclude/3', null); delete B['exclude/3'];
  nondet('select/3', function* (a, e) {
    const l = listToArray(a[1]);
    if (l) { for (let i = 0; i < l.length; i++) { const m = e.trail.length; if (e.unify(a[0], l[i]) && e.unify(a[2], list(l.slice(0, i).concat(l.slice(i + 1))))) yield; e.undo(m); } return; }
    const r = listToArray(a[2]); if (!r) throw instErr();
    for (let i = 0; i <= r.length; i++) { const m = e.trail.length; if (e.unify(a[1], list(r.slice(0, i).concat([a[0]], r.slice(i))))) yield; e.undo(m); }
  });
  det('selectchk/3', (a, e) => { const l = arr(a[1]); for (let i = 0; i < l.length; i++) { const m = e.trail.length; if (e.unify(a[0], l[i]) && e.unify(a[2], list(l.slice(0, i).concat(l.slice(i + 1))))) return true; e.undo(m); } return false; });
  nondet('permutation/2', function* (a, e) {
    const l = listToArray(a[0]) || (listToArray(a[1]) ? null : null);
    let src = l, other = a[1];
    if (!src) { src = arr(a[1]); other = a[0]; }
    const perm = function* (xs) { if (!xs.length) { yield []; return; } for (let i = 0; i < xs.length; i++) for (const r of perm(xs.slice(0, i).concat(xs.slice(i + 1)))) yield [xs[i]].concat(r); };
    for (const p of perm(src)) { const m = e.trail.length; if (e.unify(other, list(p))) yield; e.undo(m); }
  });
  det('exclude_dummy/0', () => true); delete B['exclude_dummy/0'];
  det('pairs_keys_values/3', (a, e) => { const l = listToArray(a[0]); if (l) return e.unify(a[1], list(l.map(x => D(x).a[0]))) && e.unify(a[2], list(l.map(x => D(x).a[1]))); const ks = arr(a[1]), vs = arr(a[2]); return e.unify(a[0], list(ks.map((k, i) => Cmp('-', [k, vs[i]])))); });
  det('pairs_keys/2', (a, e) => e.unify(a[1], list(arr(a[0]).map(x => D(x).a[0]))));
  det('pairs_values/2', (a, e) => e.unify(a[1], list(arr(a[0]).map(x => D(x).a[1]))));
  det('sumlist/2', B['sum_list/2'].fn);
  det('max_min_dummy/0', () => true); delete B['max_min_dummy/0'];
  det('not_member/2', (a, e) => !arr(a[1]).some(y => compare(a[0], y) === 0));
  det('tab/2', () => true);

  // higher order (expand into goals; the converter specialises them instead)
  callb('maplist/2', a => mapGoal(a, 1)); callb('maplist/3', a => mapGoal(a, 2)); callb('maplist/4', a => mapGoal(a, 3)); callb('maplist/5', a => mapGoal(a, 4));
  function mapGoal(a, k) {
    const ls = a.slice(1);
    // build lists elementwise: unify each list with skeleton of same length
    const known = ls.map(l => listToArray(l)).find(x => x);
    if (!known) {
      // fall back to recursive definition
      return Cmp('$maplist_rec', [a[0], list(ls)]);
    }
    const n = known.length; const goals = []; const skels = [];
    for (let j = 0; j < k; j++) { const vs = []; for (let i = 0; i < n; i++) vs.push(Var()); skels.push(vs); goals.push(Cmp('=', [ls[j], list(vs)])); }
    for (let i = 0; i < n; i++) goals.push(Cmp('call', [a[0]].concat(skels.map(s => s[i]))));
    return conj(goals);
  }
  callb('$maplist_rec/2', a => {
    const ls = arr(a[1]); const hs = ls.map(() => Var()), ts = ls.map(() => Var());
    const nilCase = conj(ls.map(l => Cmp('=', [l, NIL])));
    const consCase = conj(ls.map((l, i) => Cmp('=', [l, cons(hs[i], ts[i])])).concat([Cmp('call', [a[0]].concat(hs)), Cmp('$maplist_rec', [a[0], list(ts)])]));
    return Cmp(';', [nilCase, consCase]);
  });
  callb('$foldl_rec/4', a => {
    const ls = arr(a[1]); const hs = ls.map(() => Var()), ts = ls.map(() => Var()), V1 = Var();
    const nilCase = conj(ls.map(l => Cmp('=', [l, NIL])).concat([Cmp('=', [a[2], a[3]])]));
    const consCase = conj(ls.map((l, i) => Cmp('=', [l, cons(hs[i], ts[i])])).concat([Cmp('call', [a[0]].concat(hs, [a[2], V1])), Cmp('$foldl_rec', [a[0], list(ts), V1, a[3]])]));
    return Cmp(';', [nilCase, consCase]);
  });
  callb('foldl/4', a => foldGoal(a, 1)); callb('foldl/5', a => foldGoal(a, 2)); callb('foldl/6', a => foldGoal(a, 3));
  function foldGoal(a, k) {
    // the lists may be partial (as SWI-Prolog's foldl walks them): a proper one sets the length
    const raw = a.slice(1, 1 + k), known = raw.map(l => listToArray(l)).find(x => x);
    const goals = []; let acc = a[1 + k];
    if (!known) return Cmp('$foldl_rec', [a[0], list(raw), acc, a[2 + k]]);
    const n = known.length;
    const ls = raw.map(l => { const x = listToArray(l); if (x && x.length === n) return x; const vs = []; for (let i = 0; i < n; i++) vs.push(Var()); goals.push(Cmp('=', [l, list(vs)])); return vs; });
    for (let i = 0; i < n; i++) { const nx = Var(); goals.push(Cmp('call', [a[0]].concat(ls.map(l => l[i]), [acc, nx]))); acc = nx; }
    goals.push(Cmp('=', [acc, a[2 + k]]));
    return conj(goals);
  }
  callb('include/3', a => { const l = arr(a[1]); const R = a[2]; const outs = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp('=', [outs[i], list([x])])]), Cmp('=', [outs[i], NIL])])); goals.push(Cmp('append', [list(outs), R])); return conj(goals); });
  callb('exclude/3', a => { const l = arr(a[1]); const R = a[2]; const outs = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp('=', [outs[i], NIL])]), Cmp('=', [outs[i], list([x])])])); goals.push(Cmp('append', [list(outs), R])); return conj(goals); });
  callb('partition/4', a => { const l = arr(a[1]); const I = l.map(() => Var()), X = l.map(() => Var()); const goals = l.map((x, i) => Cmp(';', [Cmp('->', [Cmp('call', [a[0], x]), Cmp(',', [Cmp('=', [I[i], list([x])]), Cmp('=', [X[i], NIL])])]), Cmp(',', [Cmp('=', [I[i], NIL]), Cmp('=', [X[i], list([x])])])])); goals.push(Cmp('append', [list(I), a[2]]), Cmp('append', [list(X), a[3]])); return conj(goals); });
  // yall lambdas: copy the lambda (Free/Lambda keeps Free shared), bind parameters, call the body
  for (let n = 2; n <= 9; n++) callb('>>/' + n, a => {
    let lam = Cmp('>>', [a[0], a[1]]); const extra = a.slice(2);
    let free = null, ps = D(a[0]);
    if (ps.t === 'c' && ps.f === '/' && ps.a.length === 2) free = ps.a[0];
    const m = new Map(); if (free) for (const v of termVars(free)) m.set(v, v);
    const c = copy(lam, m); let params = D(c.a[0]); if (params.t === 'c' && params.f === '/') params = D(params.a[1]);
    const pl = listToArray(params) || [];
    const goals = [];
    pl.forEach((p, i) => { if (i < extra.length) goals.push(Cmp('=', [p, extra[i]])); });
    let body = c.a[1];
    if (extra.length > pl.length) body = Cmp('call', [body].concat(extra.slice(pl.length)));
    goals.push(body);
    return conj(goals);
  });
  callb('phrase/2', a => Cmp('call', [a[0], a[1], NIL]));
  callb('phrase/3', a => Cmp('call', [a[0], a[1], a[2]]));
  function conj(gs) { if (!gs.length) return P.TRUE; let r = gs[gs.length - 1]; for (let i = gs.length - 2; i >= 0; i--) r = Cmp(',', [gs[i], r]); return r; }

  // database
  det('assert/1', (a, e) => { e.prog.add(copy(a[0])); return true; });
  det('assertz/1', B['assert/1'].fn);
  det('asserta/1', (a, e) => { e.prog.add(copy(a[0]), null, false); return true; });
  nondet('retract/1', function* (a, e) {
    let t = D(a[0]); let h = t, b = P.TRUE; if (t.t === 'c' && t.f === ':-') { h = D(t.a[0]); b = t.a[1]; }
    const cls = e.prog.preds.get(P.key(h)); if (!cls) return;
    for (const cl of cls.slice()) { const m = e.trail.length; const mp = new Map(); if (e.unify(h, copy(cl.head, mp)) && e.unify(b, copy(cl.body, mp))) { const i = cls.indexOf(cl); if (i >= 0) cls.splice(i, 1); yield; } e.undo(m); }
  });
  det('retractall/1', (a, e) => { const h = D(a[0]); const k = P.key(h); const cls = e.prog.preds.get(k); if (!cls) { e.prog.preds.set(k, []); e.prog.dynamic.add(k); return true; } for (const cl of cls.slice()) { const m = e.trail.length; if (e.unify(h, copy(cl.head))) cls.splice(cls.indexOf(cl), 1); e.undo(m); } return true; });
  det('nb_setval/2', (a, e) => { e.globals.set(textOf(a[0]), copy(a[1])); return true; });
  det('b_setval/2', B['nb_setval/2'].fn);
  det('nb_getval/2', (a, e) => { const v = e.globals.get(textOf(a[0])); if (!v) throw new PlError(Cmp('error', [Cmp('existence_error', [Atom('variable'), a[0]]), Var()])); return e.unify(a[1], v); });
  det('b_getval/2', B['nb_getval/2'].fn);
  det('garbage_collect/0', () => true);
  det('statistics/2', (a, e) => e.unify(a[1], list([Int(Math.round(P.now())), Int(0)])));
  det('get_time/1', (a, e) => e.unify(a[0], Num(Date.now() / 1000, true)));
  det('random/1', (a, e) => e.unify(a[0], Num(Math.random(), true)));
  det('random_between/3', (a, e) => { const lo = evalArith(a[0]).v, hi = evalArith(a[1]).v; return e.unify(a[2], Int(lo + Math.floor(Math.random() * (hi - lo + 1)))); });
  det('succ_or_zero/1', () => true); delete B['succ_or_zero/1'];
  det('ensure_loaded/1', () => true);
  det('use_module/1', () => true);
  det('use_module/2', () => true);
  det('set_prolog_flag/2', () => true);
  det('style_check/1', () => true);
  det('discontiguous/1', () => true);
  det('dynamic/1', (a, e) => { for (const s of P.commaList(a[0])) { const sd = D(s); const k = P.name(sd.a[0]) + '/' + D(sd.a[1]).v; e.prog.dynamic.add(k); if (!e.prog.preds.has(k)) e.prog.preds.set(k, []); } return true; });
  det('tabling_dummy/0', () => true); delete B['tabling_dummy/0'];

  P.builtins = B;
  P.conj = conj;
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
