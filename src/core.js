/* pl2detlog core: terms, reader (tokenizer + operator-precedence parser), printer.
   BSD-3-Clause. Part of pl2detlog (Prolog -> Detlog). */
(function (P) {
  'use strict';

  // ---------- terms ----------
  let varCounter = 0;
  const atomTable = new Map();
  function Atom(n) { let a = atomTable.get(n); if (!a) { a = { t: 'a', n }; atomTable.set(n, a); } return a; }
  function Num(v, f) { return { t: 'n', v, f: !!f || !Number.isInteger(v) }; }
  function Int(v) { return { t: 'n', v, f: false }; }
  function Str(v) { return { t: 's', v }; }
  function Var(name) { return { t: 'v', name: name || null, ref: null, id: ++varCounter }; }
  function Cmp(f, a) { return a.length === 0 ? Atom(f) : { t: 'c', f, a }; }
  const NIL = Atom('[]');
  const TRUE = Atom('true');
  const FAIL = Atom('fail');
  function cons(h, t) { return { t: 'c', f: '.', a: [h, t] }; }
  function list(arr, tail) { let r = tail || NIL; for (let i = arr.length - 1; i >= 0; i--) r = cons(arr[i], r); return r; }

  function deref(t) { while (t.t === 'v' && t.ref) t = t.ref; return t; }
  function isCons(t) { return t.t === 'c' && t.f === '.' && t.a.length === 2; }
  function isNil(t) { return t.t === 'a' && t.n === '[]'; }
  function listToArray(t) { // returns array or null if not proper list
    const out = []; t = deref(t);
    while (isCons(t)) { out.push(t.a[0]); t = deref(t.a[1]); }
    return isNil(t) ? out : null;
  }
  function name(t) { t = deref(t); return t.t === 'a' ? t.n : t.t === 'c' ? t.f : null; }
  function arity(t) { t = deref(t); return t.t === 'c' ? t.a.length : 0; }
  function key(t) { t = deref(t); return t.t === 'a' ? t.n + '/0' : t.t === 'c' ? t.f + '/' + t.a.length : null; }
  function args(t) { t = deref(t); return t.t === 'c' ? t.a : []; }

  // full dereferenced copy with fresh variables (sharing preserved)
  // copy with fresh variables; ground subterms are shared, not copied (they are immutable)
  function copy(t, map) {
    map = map || new Map();
    t = deref(t);
    if (t.gr) return t;
    if (t.t === 'v') { let v = map.get(t); if (!v) { v = Var(t.name); map.set(t, v); } return v; }
    if (t.t === 'c') {
      if (t.f === '.' && t.a.length === 2) { // iterate along list spines
        const heads = [], cells = []; let x = t;
        while (x.t === 'c' && x.f === '.' && x.a.length === 2 && !x.gr) { cells.push(x); heads.push(copy(x.a[0], map)); x = deref(x.a[1]); }
        let r = copy(x, map);
        for (let i = heads.length - 1; i >= 0; i--) {
          const c = cells[i];
          if (r === c.a[1] && heads[i] === c.a[0]) { c.gr = true; r = c; } // unchanged suffix: share (deref'd tail identical)
          else r = { t: 'c', f: '.', a: [heads[i], r] };
        }
        return r;
      }
      const a = new Array(t.a.length); let same = true;
      for (let i = 0; i < a.length; i++) { a[i] = copy(t.a[i], map); if (a[i] !== t.a[i]) same = false; }
      if (same) { t.gr = true; return t; }
      return { t: 'c', f: t.f, a };
    }
    return t;
  }
  // resolve all bindings (no fresh vars)
  // resolve bindings; ground subterms are shared and marked ground (t.gr), so later copies are O(1)
  function resolve(t) {
    t = deref(t);
    if (t.t !== 'c' || t.gr) return t;
    if (t.f === '.' && t.a.length === 2) {
      const heads = [], cells = []; let x = t;
      while (x.t === 'c' && x.f === '.' && x.a.length === 2 && !x.gr) { cells.push(x); heads.push(resolve(x.a[0])); x = deref(x.a[1]); }
      let r = resolve(x);
      let g = r.t !== 'v' && (r.t !== 'c' || r.gr === true);
      for (let i = heads.length - 1; i >= 0; i--) {
        const h = heads[i], c = cells[i];
        g = g && h.t !== 'v' && (h.t !== 'c' || h.gr === true);
        if (h === c.a[0] && r === c.a[1]) { if (g) c.gr = true; r = c; }
        else { r = { t: 'c', f: '.', a: [h, r] }; if (g) r.gr = true; }
      }
      return r;
    }
    const a = new Array(t.a.length); let ch = false, g = true;
    for (let i = 0; i < a.length; i++) { const x = resolve(t.a[i]); a[i] = x; if (x !== t.a[i]) ch = true; if (x.t === 'v' || (x.t === 'c' && !x.gr)) g = false; }
    const r = ch ? { t: 'c', f: t.f, a } : t;
    if (g) r.gr = true;
    return r;
  }
  function termVars(t, acc, seen) {
    acc = acc || []; seen = seen || new Set();
    const st = [t];
    while (st.length) {
      let x = deref(st.pop());
      if (x.t === 'v') { if (!seen.has(x)) { seen.add(x); acc.push(x); } }
      else if (x.t === 'c') for (let i = x.a.length - 1; i >= 0; i--) st.push(x.a[i]);
    }
    return acc;
  }
  function isGround(t) {
    const st = [t];
    while (st.length) { const x = deref(st.pop()); if (x.t === 'v') return false; if (x.t === 'c') for (const y of x.a) st.push(y); }
    return true;
  }

  // ---------- standard order ----------
  function typeRank(t) { switch (t.t) { case 'v': return 0; case 'n': return 1; case 'a': return 3; case 's': return 4; default: return 5; } }
  function compare(a, b) {
    a = deref(a); b = deref(b);
    if (a === b) return 0;
    const ra = typeRank(a), rb = typeRank(b);
    if (ra !== rb) return ra < rb ? -1 : 1;
    switch (a.t) {
      case 'v': return a.id < b.id ? -1 : 1;
      case 'n': if (a.v !== b.v) return a.v < b.v ? -1 : 1; if (a.f !== b.f) return a.f ? -1 : 1; return 0;
      case 'a': return a.n < b.n ? -1 : a.n > b.n ? 1 : 0;
      case 's': return a.v < b.v ? -1 : a.v > b.v ? 1 : 0;
      case 'c':
        if (a.a.length !== b.a.length) return a.a.length < b.a.length ? -1 : 1;
        if (a.f !== b.f) return a.f < b.f ? -1 : 1;
        for (let i = 0; i < a.a.length; i++) { const c = compare(a.a[i], b.a[i]); if (c) return c; }
        return 0;
    }
    return 0;
  }
  // variant key: canonical string, variables numbered by first occurrence
  function variantKey(t) {
    const m = new Map(); let n = 0; const parts = [];
    (function walk(x) {
      x = deref(x);
      switch (x.t) {
        case 'v': { let k = m.get(x); if (k === undefined) { k = n++; m.set(x, k); } parts.push('_' + k); break; }
        case 'n': parts.push((x.f ? 'f' : 'i') + x.v); break;
        case 'a': parts.push('a' + JSON.stringify(x.n)); break;
        case 's': parts.push('s' + JSON.stringify(x.v)); break;
        case 'c': parts.push('c' + JSON.stringify(x.f) + x.a.length + '('); for (const y of x.a) walk(y); parts.push(')'); break;
      }
    })(t);
    return parts.join(' ');
  }

  // ---------- operators ----------
  const ops = {
    prefix: new Map(), infix: new Map(), postfix: new Map()
  };
  function addOp(p, type, nm) {
    const tbl = type.length === 2 ? (type[0] === 'f' ? ops.prefix : ops.postfix) : ops.infix;
    if (p === 0) tbl.delete(nm); else tbl.set(nm, { p, type });
  }
  [[1200, 'xfx', [':-', '-->']], [1200, 'fx', [':-', '?-']], [1100, 'xfy', [';', '|']], [1105, 'xfy', ['|']],
   [1050, 'xfy', ['->', '*->']], [1000, 'xfy', [',']], [990, 'xfx', [':=']], [900, 'fy', ['\\+']],
   [700, 'xfx', ['=', '\\=', '==', '\\==', '@<', '@>', '@=<', '@>=', '=..', 'is', '=:=', '=\\=', '<', '>', '=<', '>=', '>:<', ':<', 'as']],
   [600, 'xfy', [':']], [500, 'yfx', ['+', '-', '/\\', '\\/', 'xor']], [500, 'fx', ['?']],
   [400, 'yfx', ['*', '/', '//', 'rem', 'mod', 'div', '<<', '>>', 'divmod', 'rdiv']],
   [200, 'xfx', ['**']], [200, 'xfy', ['^']], [200, 'fy', ['-', '+', '\\']], [100, 'yfx', ['.']], [1, 'fx', ['$']],
   [1150, 'fx', ['dynamic', 'discontiguous', 'initialization', 'module_transparent', 'multifile', 'public', 'thread_local', 'table']]
  ].forEach(([p, ty, ns]) => ns.forEach(n => addOp(p, ty, n)));
  ops.infix.set(',', { p: 1000, type: 'xfy' });

  // ---------- tokenizer ----------
  const SYM = '+-*/\\^<>=~:.?@#&$';
  const isSym = c => SYM.indexOf(c) >= 0;
  const isAlnum = c => /[A-Za-z0-9_]/.test(c);
  function PrologSyntaxError(msg, pos, src) {
    const line = src ? src.slice(0, pos).split('\n').length : 0;
    const e = new Error('Syntax error' + (line ? ' (line ' + line + ')' : '') + ': ' + msg);
    e.prolog = true; e.pos = pos; e.line = line; return e;
  }
  function tokenize(src) {
    const toks = []; let i = 0; const n = src.length;
    let layoutBefore = true;
    while (i < n) {
      const c = src[i];
      if (/\s/.test(c)) { i++; layoutBefore = true; continue; }
      if (c === '%') { while (i < n && src[i] !== '\n') i++; layoutBefore = true; continue; }
      if (c === '/' && src[i + 1] === '*') { const j = src.indexOf('*/', i + 2); if (j < 0) throw PrologSyntaxError('unterminated block comment', i, src); i = j + 2; layoutBefore = true; continue; }
      const start = i; const lb = layoutBefore; layoutBefore = false;
      if (/[0-9]/.test(c)) {
        if (c === '0' && src[i + 1] === "'") {
          i += 2; let ch = src[i];
          if (ch === '\\') { const r = readEscape(src, i + 1); toks.push({ k: 'num', v: r.ch.codePointAt(0), pos: start, lb }); i = r.i; continue; }
          if (ch === "'" && src[i + 1] === "'") { toks.push({ k: 'num', v: 39, pos: start, lb }); i += 2; continue; }
          const cp = src.codePointAt(i); toks.push({ k: 'num', v: cp, pos: start, lb }); i += cp > 0xffff ? 2 : 1; continue;
        }
        if (c === '0' && /[xob]/.test(src[i + 1] || '') ) {
          const base = { x: 16, o: 8, b: 2 }[src[i + 1]]; const re = base === 16 ? /[0-9a-fA-F]/ : base === 8 ? /[0-7]/ : /[01]/;
          let j = i + 2; while (j < n && re.test(src[j])) j++;
          if (j > i + 2) { toks.push({ k: 'num', v: parseInt(src.slice(i + 2, j), base), pos: start, lb }); i = j; continue; }
        }
        let j = i; while (j < n && /[0-9_]/.test(src[j])) j++;
        let isF = false;
        if (src[j] === '.' && /[0-9]/.test(src[j + 1] || '')) { isF = true; j++; while (j < n && /[0-9]/.test(src[j])) j++; }
        if ((src[j] === 'e' || src[j] === 'E') && /[0-9+-]/.test(src[j + 1] || '')) {
          let k = j + 1; if (src[k] === '+' || src[k] === '-') k++;
          if (/[0-9]/.test(src[k] || '')) { isF = true; j = k; while (j < n && /[0-9]/.test(src[j])) j++; }
        }
        const text = src.slice(i, j).replace(/_/g, '');
        toks.push({ k: 'num', v: isF ? parseFloat(text) : parseInt(text, 10), f: isF, pos: start, lb }); i = j; continue;
      }
      if (c === '_' || /[A-Z]/.test(c)) { let j = i; while (j < n && isAlnum(src[j])) j++; toks.push({ k: 'var', v: src.slice(i, j), pos: start, lb }); i = j; continue; }
      if (/[a-z]/.test(c)) { let j = i; while (j < n && isAlnum(src[j])) j++; toks.push({ k: 'atom', v: src.slice(i, j), pos: start, lb }); i = j; continue; }
      if (c === "'" || c === '"' || c === '`') {
        const q = c; let j = i + 1; let s = '';
        for (;;) {
          if (j >= n) throw PrologSyntaxError('unterminated quoted', i, src);
          const d = src[j];
          if (d === q) { if (src[j + 1] === q) { s += q; j += 2; continue; } j++; break; }
          if (d === '\\') {
            if (src[j + 1] === '\n') { j += 2; continue; }
            const r = readEscape(src, j + 1); s += r.ch; j = r.i; continue;
          }
          s += d; j++;
        }
        toks.push({ k: q === "'" ? 'qatom' : q === '"' ? 'str' : 'bq', v: s, pos: start, lb }); i = j; continue;
      }
      if (c === '(' || c === ')' || c === '[' || c === ']' || c === '{' || c === '}' || c === ',' || c === '|') {
        if (c === '|' && src[i + 1] === '|') { toks.push({ k: 'atom', v: '||', pos: start, lb }); i += 2; continue; }
        toks.push({ k: 'punct', v: c, pos: start, lb }); i++; continue;
      }
      if (c === '!' || c === ';') { toks.push({ k: 'atom', v: c, pos: start, lb }); i++; continue; }
      if (isSym(c)) {
        let j = i; while (j < n && isSym(src[j])) j++;
        const text = src.slice(i, j);
        if (text === '.' && (j >= n || /\s|%/.test(src[j]))) { toks.push({ k: 'end', pos: start, lb }); i = j; continue; }
        toks.push({ k: 'atom', v: text, pos: start, lb }); i = j; continue;
      }
      throw PrologSyntaxError('unexpected character ' + JSON.stringify(c), i, src);
    }
    toks.push({ k: 'eof', pos: n });
    return toks;
  }
  function readEscape(src, i) {
    const c = src[i];
    const simple = { n: '\n', t: '\t', r: '\r', a: '\x07', b: '\b', f: '\f', v: '\v', '0': '\0', '\\': '\\', "'": "'", '"': '"', '`': '`', e: '\x1b', s: ' ' };
    if (c === 'x') { let j = i + 1; let h = ''; while (/[0-9a-fA-F]/.test(src[j])) h += src[j++]; if (src[j] === '\\') j++; return { ch: String.fromCodePoint(parseInt(h, 16)), i: j }; }
    if (/[0-7]/.test(c)) { let j = i; let o = ''; while (/[0-7]/.test(src[j])) o += src[j++]; if (src[j] === '\\') j++; return { ch: String.fromCodePoint(parseInt(o, 8)), i: j }; }
    if (c in simple) return { ch: simple[c], i: i + 1 };
    return { ch: c, i: i + 1 };
  }

  // ---------- parser ----------
  function Parser(src) { this.src = src; this.toks = tokenize(src); this.i = 0; this.varMap = null; this.varNames = null; }
  Parser.prototype.peek = function () { return this.toks[this.i]; };
  Parser.prototype.next = function () { return this.toks[this.i++]; };
  Parser.prototype.err = function (msg, tok) { throw PrologSyntaxError(msg, (tok || this.peek()).pos, this.src); };
  Parser.prototype.expect = function (k, v) { const t = this.next(); if (t.k !== k || (v !== undefined && t.v !== v)) this.err('expected ' + (v || k), t); return t; };
  Parser.prototype.readClause = function () {
    if (this.peek().k === 'eof') return null;
    this.varMap = new Map(); this.varNames = [];
    const t = this.parse(1200);
    this.expect('end');
    return { term: t, vars: this.varNames.slice() };
  };
  Parser.prototype.mkVar = function (nm) {
    if (nm === '_') return Var('_');
    let v = this.varMap.get(nm); if (!v) { v = Var(nm); this.varMap.set(nm, v); this.varNames.push([nm, v]); }
    return v;
  };
  function isTermStart(tok) {
    if (!tok) return false;
    if (tok.k === 'eof' || tok.k === 'end') return false;
    if (tok.k === 'punct') return tok.v === '(' || tok.v === '[' || tok.v === '{';
    if (tok.k === 'atom' && ops.infix.has(tok.v) && !ops.prefix.has(tok.v)) return false;
    return true;
  }
  Parser.prototype.parsePrimary = function (maxPrec) {
    const tok = this.next();
    switch (tok.k) {
      case 'num': return { term: Num(tok.v, tok.f), prec: 0 };
      case 'var': return { term: this.mkVar(tok.v), prec: 0 };
      case 'str': return { term: Str(tok.v), prec: 0 };
      case 'bq': return { term: list([...tok.v].map(ch => Int(ch.codePointAt(0)))), prec: 0 };
      case 'punct':
        if (tok.v === '(') { const t = this.parse(1200); this.expect('punct', ')'); return { term: t, prec: 0 }; }
        if (tok.v === '[') {
          if (this.peek().k === 'punct' && this.peek().v === ']') { this.next(); return this.afterAtom('[]', tok, maxPrec); }
          const items = [this.parse(999)]; let tail = NIL;
          for (;;) {
            const p = this.peek();
            if (p.k === 'punct' && p.v === ',') { this.next(); items.push(this.parse(999)); continue; }
            if (p.k === 'punct' && p.v === '|') { this.next(); tail = this.parse(999); }
            break;
          }
          this.expect('punct', ']');
          return { term: list(items, tail), prec: 0 };
        }
        if (tok.v === '{') {
          if (this.peek().k === 'punct' && this.peek().v === '}') { this.next(); return this.afterAtom('{}', tok, maxPrec); }
          const t = this.parse(1200); this.expect('punct', '}'); return { term: Cmp('{}', [t]), prec: 0 };
        }
        if (tok.v === ',') this.err('unexpected comma', tok);
        if (tok.v === '|') return this.afterAtom('|', tok, maxPrec);
        this.err('unexpected ' + tok.v, tok);
        break;
      case 'atom': case 'qatom': return this.afterAtom(tok.v, tok, maxPrec);
      case 'end': this.err('unexpected end of clause', tok); break;
      default: this.err('unexpected end of input', tok);
    }
  };
  Parser.prototype.afterAtom = function (nm, tok, maxPrec) {
    const p = this.peek();
    if (p.k === 'punct' && p.v === '(' && !p.lb) {
      this.next(); const a = [this.parse(999)];
      while (this.peek().k === 'punct' && this.peek().v === ',') { this.next(); a.push(this.parse(999)); }
      this.expect('punct', ')');
      return { term: Cmp(nm, a), prec: 0 };
    }
    if (tok.k === 'atom' && nm === '-' && p.k === 'num' && !p.lb) { this.next(); return { term: Num(-p.v, p.f), prec: 0 }; }
    if (tok.k === 'atom' && ops.prefix.has(nm)) {
      const op = ops.prefix.get(nm);
      const nx = this.peek();
      let operand = isTermStart(nx);
      if (operand && nx.k === 'atom' && ops.infix.has(nx.v)) {
        // `- = x` : prefix op followed by an infix op -> treat as atom, unless the infix atom is a term itself (f( or prefix op)
        const n2 = this.toks[this.i + 1];
        const isFunctor = n2 && n2.k === 'punct' && n2.v === '(' && !n2.lb;
        if (!isFunctor && !ops.prefix.has(nx.v)) operand = false;
      }
      if (operand) {
        let p2 = op.p; if (p2 > maxPrec) p2 = 999;
        const argMax = op.type === 'fy' ? p2 : p2 - 1;
        const save = this.i;
        try { const arg = this.parse(argMax); return { term: Cmp(nm, [arg]), prec: p2 }; }
        catch (e) { this.i = save; }
      }
      return { term: Atom(nm), prec: op.p > maxPrec ? 0 : op.p };
    }
    const pr = (ops.infix.has(nm) || ops.prefix.has(nm)) ? Math.max(ops.infix.has(nm) ? ops.infix.get(nm).p : 0, 0) : 0;
    return { term: Atom(nm), prec: pr > maxPrec ? 0 : pr };
  };
  Parser.prototype.parse = function (maxPrec) {
    let { term: left, prec: leftPrec } = this.parsePrimary(maxPrec);
    for (;;) {
      const tok = this.peek();
      let nm = null;
      if (tok.k === 'atom') nm = tok.v;
      else if (tok.k === 'punct' && (tok.v === ',' || tok.v === '|')) nm = tok.v;
      else break;
      const op = ops.infix.get(nm);
      if (op) {
        const p = op.p;
        const la = op.type[0] === 'y' ? p : p - 1;
        const ra = op.type[2] === 'y' ? p : p - 1;
        if (p <= maxPrec && leftPrec <= la) {
          this.next();
          const right = this.parse(ra);
          const f = nm === '|' ? ';' : nm;
          left = Cmp(f, [left, right]); leftPrec = p; continue;
        }
      }
      const pop = ops.postfix.get(nm);
      if (pop && pop.p <= maxPrec) { this.next(); left = Cmp(nm, [left]); leftPrec = pop.p; continue; }
      break;
    }
    return left;
  };

  function readProgram(src) {
    const p = new Parser(src); const out = [];
    for (;;) {
      const c = p.readClause(); if (!c) break;
      const t = c.term;
      if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
        const d = deref(t.a[0]);
        if (d.t === 'c' && d.f === 'op' && d.a.length === 3) {
          const pr = deref(d.a[0]).v, ty = deref(d.a[1]).n; const nmT = deref(d.a[2]);
          const names = listToArray(nmT) || [nmT];
          names.forEach(x => addOp(pr, ty, deref(x).n));
        }
      }
      out.push(c);
    }
    return out;
  }
  function readTerm(src) {
    const s = src.trim().replace(/\.\s*$/, '');
    const p = new Parser(s + ' .'); const c = p.readClause(); if (!c) throw PrologSyntaxError('empty term', 0, src);
    return c;
  }

  // ---------- printer ----------
  function atomNeedsQuote(n) {
    if (n === '[]' || n === '!' || n === ';' || n === '{}' || n === ',') return n === ',';
    if (/^[a-z][A-Za-z0-9_]*$/.test(n)) return false;
    if (/^[+\-*/\\^<>=~:.?@#&$]+$/.test(n)) return false;
    return true;
  }
  function quoteAtom(n) {
    return "'" + n.replace(/\\/g, '\\\\').replace(/'/g, "\\'").replace(/\n/g, '\\n').replace(/\t/g, '\\t') + "'";
  }
  function fmtAtom(n, q) { return q && atomNeedsQuote(n) ? quoteAtom(n) : n; }
  function fmtNum(t) {
    if (t.f) { let s = String(t.v); if (!/[.eE]/.test(s) && isFinite(t.v)) s += '.0'; if (s === 'Infinity') s = 'inf'; if (s === '-Infinity') s = '-inf'; if (s === 'NaN') s = 'nan'; return s; }
    return String(t.v);
  }
  // opts: {quoted, varName: fn(v)->string, ignoreOps}
  function show(t, opts) {
    opts = opts || {};
    const q = opts.quoted !== false;
    const vn = opts.varName || (v => v.name && v.name !== '_' ? v.name : '_G' + v.id);
    function w(t, maxP) {
      t = deref(t);
      switch (t.t) {
        case 'v': return vn(t);
        case 'n': { const s = fmtNum(t); return s; }
        case 's': return q ? JSON.stringify(t.v) : t.v;
        case 'a': { const s = fmtAtom(t.n, q); if ((ops.infix.has(t.n) || ops.prefix.has(t.n)) && maxP < 1200 && t.n !== '[]' && t.n !== '{}' && t.n !== '!' && t.n !== ';') { const p = Math.max(ops.infix.has(t.n) ? ops.infix.get(t.n).p : 0, ops.prefix.has(t.n) ? ops.prefix.get(t.n).p : 0); if (p > maxP) return '(' + s + ')'; } return s; }
        case 'c': {
          if (t.f === '.' && t.a.length === 2) {
            const items = []; let x = t;
            while (x.t === 'c' && x.f === '.' && x.a.length === 2) { items.push(w(x.a[0], 999)); x = deref(x.a[1]); }
            let s = '[' + items.join(', ');
            if (!(x.t === 'a' && x.n === '[]')) s += '|' + w(x, 999);
            return s + ']';
          }
          if (t.f === '{}' && t.a.length === 1) return '{' + w(t.a[0], 1200) + '}';
          if (!opts.ignoreOps && t.a.length === 2 && ops.infix.has(t.f)) {
            const op = ops.infix.get(t.f); const p = op.p;
            const lp = op.type[0] === 'y' ? p : p - 1, rp = op.type[2] === 'y' ? p : p - 1;
            let l = w(t.a[0], lp), r = w(t.a[1], rp);
            let s;
            if (t.f === ',') s = l + ', ' + r;
            else if (/^[a-z]/.test(t.f) || ['->', ':-', '-->', ';', '*->', 'is', '=', '\\=', '==', '\\==', '=..', '<', '>', '=<', '>=', '=:=', '=\\=', '@<', '@>', '@=<', '@>='].includes(t.f) || p >= 700) s = l + ' ' + fmtAtom(t.f, q) + ' ' + r;
            else {
              // avoid gluing symbol chars, e.g. 1- -1, a- (-b)
              const ft = fmtAtom(t.f, q);
              const glueR = isSym(ft[ft.length - 1]) && (isSym(r[0]) || /^-?\d/.test(r) && r[0] === '-');
              const glueL = isSym(ft[0]) && isSym(l[l.length - 1]);
              s = l + (glueL ? ' ' : '') + ft + (glueR ? ' ' : '') + r;
            }
            return p > maxP ? '(' + s + ')' : s;
          }
          if (!opts.ignoreOps && t.a.length === 1 && ops.prefix.has(t.f) && t.f !== '-' && t.f !== '+' || (!opts.ignoreOps && t.a.length === 1 && (t.f === '-' || t.f === '+'))) {
            const op = ops.prefix.get(t.f);
            if (op) {
              const p = op.p; const ap = op.type === 'fy' ? p : p - 1;
              const a0 = deref(t.a[0]);
              let as = w(a0, ap);
              const ft = fmtAtom(t.f, q);
              const needSpace = /^[a-z]/i.test(ft) || ft === '\\+' || isSym(ft[ft.length - 1]) && (isSym(as[0]) || a0.t === 'n') || as[0] === '(';
              const s = ft + (needSpace ? ' ' : '') + as;
              return p > maxP ? '(' + s + ')' : s;
            }
          }
          return fmtAtom(t.f, q) + '(' + t.a.map(x => w(x, 999)).join(', ') + ')';
        }
      }
      return '?';
    }
    return w(t, opts.prec || 1200);
  }
  // names variables of a term _A,_B.. (or by provided names) for output
  function namer(namesMap) {
    const m = new Map(); let k = 0;
    return v => {
      if (namesMap && namesMap.has(v)) return namesMap.get(v);
      let s = m.get(v);
      if (!s) { s = '_' + letters(k++); m.set(v, s); }
      return s;
    };
  }
  function letters(k) { let s = ''; do { s = String.fromCharCode(65 + (k % 26)) + s; k = Math.floor(k / 26) - 1; } while (k >= 0); return s; }

  // pretty-print a clause with indentation of control constructs
  function showClause(cl, opts) {
    opts = opts || {};
    const vn = opts.varName || namer();
    const o = { varName: vn, quoted: true };
    cl = deref(cl);
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 2) {
      const body = deref(cl.a[1]);
      if (body.t === 'a' && body.n === 'true') return show(cl.a[0], Object.assign({ prec: 1199 }, o)) + '.';
      return show(cl.a[0], Object.assign({ prec: 1199 }, o)) + ' :-\n' + showBody(body, 1, o) + '.';
    }
    if (cl.t === 'c' && cl.f === ':-' && cl.a.length === 1) return ':- ' + show(cl.a[0], Object.assign({ prec: 1199 }, o)) + '.';
    return show(cl, Object.assign({ prec: 1199 }, o)) + '.';
  }
  function showBody(b, d, o) {
    const ind = '    '.repeat(d);
    b = deref(b);
    if (b.t === 'c' && b.f === ',' && b.a.length === 2) return showBody(b.a[0], d, o) + ',\n' + showBody(b.a[1], d, o);
    if (b.t === 'c' && (b.f === ';' || b.f === '->' || b.f === '*->') && b.a.length === 2) {
      return ind + '(   ' + showDisj(b, d, o).replace(/^\s+/, '') + '\n' + ind + ')';
    }
    if (b.t === 'c' && b.f === 'if_commit' && b.a.length === 3 && o.layoutIfCommit !== false) {
      const inner = '    '.repeat(d + 1);
      return ind + 'if_commit(\n' + showGoalBlock(b.a[0], d + 1, o) + ',\n' + showGoalBlock(b.a[1], d + 1, o) + ',\n' + showGoalBlock(b.a[2], d + 1, o) + '\n' + ind + ')';
    }
    return ind + show(b, Object.assign({ prec: 999 }, o));
  }
  function showGoalBlock(g, d, o) {
    g = deref(g);
    if (g.t === 'c' && g.f === ',' && g.a.length === 2) {
      const ind = '    '.repeat(d);
      return ind + '(\n' + showBody(g, d + 1, o) + '\n' + ind + ')';
    }
    return showBody(g, d, o);
  }
  function showDisj(b, d, o) {
    const ind = '    '.repeat(d);
    b = deref(b);
    if (b.t === 'c' && b.f === ';' && b.a.length === 2) {
      return showDisj(b.a[0], d, o) + '\n' + ind + ';   ' + showDisj(b.a[1], d, o).replace(/^\s+/, '');
    }
    if (b.t === 'c' && (b.f === '->' || b.f === '*->') && b.a.length === 2) {
      return showBody(b.a[0], d + 1, o).replace(/^\s+/, '') + '\n' + ind + b.f + '  ' + showBody(b.a[1], d + 1, o).replace(/^\s+/, '');
    }
    return showBody(b, d + 1, o).replace(/^\s+/, '');
  }

  Object.assign(P, {
    Atom, Num, Int, Str, Var, Cmp, NIL, TRUE, FAIL, cons, list, deref, isCons, isNil, listToArray,
    name, arity, key, args, copy, resolve, termVars, isGround, compare, variantKey,
    ops, addOp, tokenize, Parser, readProgram, readTerm, show, showClause, namer, letters, PrologSyntaxError,
    atomNeedsQuote, fmtAtom
  });
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
