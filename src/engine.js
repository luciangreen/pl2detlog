/* pl2detlog reference engine: ordinary Prolog semantics (cut, backtracking) with
   step / choicepoint counting.  It is the oracle that every conversion is checked against. */
(function (P) {
  'use strict';
  const { Atom, Num, Int, Str, Var, Cmp, NIL, cons, list, deref, isCons, isNil, listToArray, copy, termVars, isGround, compare, show } = P;

  function PlError(term) { this.term = term; this.prolog = true; this.message = 'Prolog error: ' + show(term); }
  PlError.prototype = Object.create(Error.prototype);
  function typeError(type, culprit) { return new PlError(Cmp('error', [Cmp('type_error', [Atom(type), culprit]), Var()])); }
  function instErr() { return new PlError(Cmp('error', [Atom('instantiation_error'), Var()])); }
  function existErr(k) { const [n, a] = splitKey(k); return new PlError(Cmp('error', [Cmp('existence_error', [Atom('procedure'), Cmp('/', [Atom(n), Int(+a)])]), Var()])); }
  function evalErr(e) { return new PlError(Cmp('error', [Cmp('evaluation_error', [Atom(e)]), Var()])); }
  function splitKey(k) { const i = k.lastIndexOf('/'); return [k.slice(0, i), k.slice(i + 1)]; }
  class LimitError extends Error { constructor(m) { super(m); this.limit = true; } }

  // ---------- program ----------
  function Program() { this.preds = new Map(); this.order = []; this.dynamic = new Set(); this.directives = []; this.clauses = []; }
  Program.prototype.add = function (term, vars, atEnd) {
    term = deref(term);
    if (P.expandDots && P.hasDots(term)) term = P.expandDots(term);
    let head = term, body = P.TRUE;
    if (term.t === 'c' && term.f === ':-' && term.a.length === 2) { head = deref(term.a[0]); body = term.a[1]; }
    else if (term.t === 'c' && term.f === ':-' && term.a.length === 1) { this.directives.push(term.a[0]); return; }
    else if (term.t === 'c' && term.f === '-->' && term.a.length === 2) { const t = dcgTransform(term); return this.add(t, vars, atEnd); }
    // Module:Head defines Head (modules are flat here; src/swi.js renames private predicates)
    while (head.t === 'c' && head.f === ':' && head.a.length === 2 && deref(head.a[0]).t === 'a') head = deref(head.a[1]);
    if (head.t === 'v') throw new Error('clause head is a variable');
    if (head.t !== 'a' && head.t !== 'c') throw new Error('clause head is not callable: ' + show(head));
    const k = P.key(head);
    if (!this.preds.has(k)) { this.preds.set(k, []); this.order.push(k); }
    const cl = { head, body, vars: vars || null, nvars: termVars(Cmp('-', [head, body])).length };
    if (atEnd === false) this.preds.get(k).unshift(cl); else this.preds.get(k).push(cl);
    this.clauses.push(cl);
    return cl;
  };
  function loadProgram(src) {
    const prog = new Program();
    const cls = typeof src === 'string' ? P.readProgram(src) : src;
    for (const c of cls) {
      const t = deref(c.term);
      if (t.t === 'c' && t.f === ':-' && t.a.length === 1) {
        const d = deref(t.a[0]);
        if (d.t === 'c' && d.f === 'dynamic') { for (const s of commaList(d.a[0])) { const sd = deref(s); if (sd.t === 'c' && sd.f === '/') { const k = P.name(sd.a[0]) + '/' + deref(sd.a[1]).v; prog.dynamic.add(k); if (!prog.preds.has(k)) { prog.preds.set(k, []); prog.order.push(k); } } } }
        prog.directives.push(d);
        continue;
      }
      prog.add(t, c.vars);
    }
    return prog;
  }
  function commaList(t) { t = deref(t); const out = []; while (t.t === 'c' && t.f === ',' && t.a.length === 2) { out.push(t.a[0]); t = deref(t.a[1]); } const l = listToArray(t); if (l) return out.concat(l); out.push(t); return out; }

  // DCG translation
  function dcgTransform(rule) {
    const head = deref(rule.a[0]), body = rule.a[1];
    const S0 = Var('S0'), S = Var('S');
    let pushback = null, h = head;
    if (h.t === 'c' && h.f === ',' ) { pushback = h.a[1]; h = deref(h.a[0]); }
    const nh = addArgs(h, S0, S);
    if (pushback) { const M = Var(); return Cmp(':-', [nh, Cmp(',', [dcgBody(body, S0, M), terminals(pushback, S, M)])]); }
    return Cmp(':-', [nh, dcgBody(body, S0, S)]);
  }
  function addArgs(t, a, b) { t = deref(t); if (t.t === 'a') return Cmp(t.n, [a, b]); if (t.t === 'c') return Cmp(t.f, t.a.concat([a, b])); throw new Error('bad DCG head'); }
  function terminals(lst, S0, S) { const arr = listToArray(lst); return Cmp('=', [S0, list(arr, S)]); }
  function dcgBody(b, S0, S) {
    b = deref(b);
    if (b.t === 'v') return Cmp('phrase', [b, S0, S]);
    if (b.t === 'c' && b.f === ',' && b.a.length === 2) { const M = Var(); return Cmp(',', [dcgBody(b.a[0], S0, M), dcgBody(b.a[1], M, S)]); }
    if (b.t === 'c' && (b.f === ';' || b.f === '|') && b.a.length === 2) return Cmp(';', [dcgBody(b.a[0], S0, S), dcgBody(b.a[1], S0, S)]);
    if (b.t === 'c' && b.f === '->' && b.a.length === 2) { const M = Var(); return Cmp('->', [dcgBody(b.a[0], S0, M), dcgBody(b.a[1], M, S)]); }
    if (b.t === 'c' && b.f === '\\+' && b.a.length === 1) return Cmp(',', [Cmp('\\+', [dcgBody(b.a[0], S0, Var())]), Cmp('=', [S0, S])]);
    if (b.t === 'a' && b.n === '!') return Cmp(',', [Atom('!'), Cmp('=', [S0, S])]);
    if (b.t === 'a' && b.n === '[]') return Cmp('=', [S0, S]);
    if (b.t === 'c' && b.f === '{}' && b.a.length === 1) return Cmp(',', [b.a[0], Cmp('=', [S0, S])]);
    if (isCons(b)) return terminals(b, S0, S);
    if (b.t === 's') return terminals(list([...b.v].map(c => Int(c.codePointAt(0)))), S0, S);
    if (b.t === 'c' && b.f === 'call') return Cmp('call', b.a.concat([S0, S]));
    return addArgs(b, S0, S);
  }

  // ---------- arithmetic ----------
  function evalArith(t) {
    t = deref(t);
    switch (t.t) {
      case 'n': return t;
      case 'v': throw instErr();
      case 's': if (t.v.length === 1) return Int(t.v.codePointAt(0)); throw typeError('evaluable', t);
      case 'a': {
        switch (t.n) {
          case 'pi': return Num(Math.PI, true); case 'e': return Num(Math.E, true);
          case 'inf': case 'infinite': return Num(Infinity, true); case 'nan': return Num(NaN, true);
          case 'max_tagged_integer': return Int(Number.MAX_SAFE_INTEGER); case 'epsilon': return Num(Number.EPSILON, true);
          case 'random': return Num(Math.random(), true); case 'random_float': return Num(Math.random(), true);
          case 'cputime': return Num(now() / 1000, true); case 'realtime': return Int(Math.floor(Date.now() / 1000));
          case '[]': break;
        }
        throw typeError('evaluable', Cmp('/', [t, Int(0)]));
      }
      case 'c': {
        if (t.f === '.' && t.a.length === 2 && isNil(deref(t.a[1]))) return evalArith(t.a[0]);
        const xs = t.a.map(evalArith);
        const a = xs[0], b = xs[1];
        const fl = xs.some(x => x.f);
        // integers are unbounded (BigInt beyond the safe range); fa, fb: the values as JS numbers, for floats
        const fa = a && typeof a.v === 'bigint' ? Number(a.v) : a && a.v, fb = b && typeof b.v === 'bigint' ? Number(b.v) : b && b.v;
        const big = x => BigInt(x.v);
        // an exact integer result: JS numbers while the result is safe, BigInt otherwise
        const iop = (f, g) => { if (typeof a.v === 'number' && (!b || typeof b.v === 'number')) { const r = f(a.v, b && b.v); if (Number.isSafeInteger(r)) return Int(r); } return Int(g(big(a), b && big(b))); };
        const needInt = () => { for (const x of xs) if (x.f) throw typeError('integer', x); };
        const isZero = x => x.v === 0 || x.v === 0n;
        const small = typeof a.v === 'number' && b && typeof b.v === 'number';
        const neg = x => x.v < 0;
        if (t.a.length === 1) switch (t.f) {
          case '-': return a.f ? Num(-a.v, true) : Int(-a.v);
          case '+': return a;
          case 'abs': return a.f ? Num(Math.abs(a.v), true) : neg(a) ? Int(-a.v) : a;
          case 'sign': return a.f ? Num(Math.sign(a.v), true) : Int(neg(a) ? -1 : isZero(a) ? 0 : 1);
          case 'min': case 'max': break;
          case 'sqrt': return Num(Math.sqrt(fa), true);
          case 'sin': return Num(Math.sin(fa), true); case 'cos': return Num(Math.cos(fa), true); case 'tan': return Num(Math.tan(fa), true);
          case 'asin': return Num(Math.asin(fa), true); case 'acos': return Num(Math.acos(fa), true); case 'atan': return Num(Math.atan(fa), true);
          case 'exp': return Num(Math.exp(fa), true);
          case 'log': if (fa <= 0) throw evalErr('undefined'); return Num(Math.log(fa), true);
          case 'log2': return Num(Math.log2(fa), true);
          case 'float': return Num(fa, true);
          case 'integer': return a.f ? Int(roundBig(a.v)) : a;
          case 'float_integer_part': return Num(Math.trunc(fa), true);
          case 'float_fractional_part': return Num(fa - Math.trunc(fa), true);
          case 'truncate': return a.f ? Int(toBig(Math.trunc(a.v))) : a;
          case 'round': return a.f ? Int(roundBig(a.v)) : a;
          case 'ceiling': return a.f ? Int(toBig(Math.ceil(a.v))) : a;
          case 'floor': return a.f ? Int(toBig(Math.floor(a.v))) : a;
          case '\\': needInt(); return Int(~big(a));
          case 'msb': needInt(); return Int(big(a).toString(2).length - 1);
          case 'succ': needInt(); return iop(x => x + 1, x => x + 1n);
          case 'random': needInt(); return Int(Math.floor(Math.random() * fa));
          case 'random_float': return Num(Math.random(), true);
        }
        if (t.a.length === 2) switch (t.f) {
          case '+': return fl ? Num(fa + fb, true) : iop((x, y) => x + y, (x, y) => x + y);
          case '-': return fl ? Num(fa - fb, true) : iop((x, y) => x - y, (x, y) => x - y);
          case '*': return fl ? Num(fa * fb, true) : iop((x, y) => x * y, (x, y) => x * y);
          case '/': if (isZero(b) && !fl) throw evalErr('zero_divisor'); if (!fl) { if (small) return a.v % b.v === 0 ? Int(a.v / b.v) : Num(a.v / b.v, true); if (big(a) % big(b) === 0n) return Int(big(a) / big(b)); return Num(fa / fb, true); } if (fb === 0) throw evalErr('zero_divisor'); return Num(fa / fb, true);
          case '//': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return iop((x, y) => Math.trunc(x / y), (x, y) => x / y);
          case 'div': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return small ? Int(Math.floor(a.v / b.v)) : Int(floorDiv(big(a), big(b)));
          case 'mod': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); if (small) { const m = a.v % b.v; return Int(m !== 0 && (m < 0) !== (b.v < 0) ? m + b.v : m); } { const m = big(a) % big(b); return Int(m !== 0n && (m < 0n) !== (big(b) < 0n) ? m + big(b) : m); }
          case 'rem': needInt(); if (isZero(b)) throw evalErr('zero_divisor'); return small ? Int(a.v % b.v) : Int(big(a) % big(b));
          case 'min': return compareNum(a, b) <= 0 ? a : b;
          case 'max': return compareNum(a, b) >= 0 ? a : b;
          case '**': if (!fl && !neg(b)) return Int(big(a) ** big(b)); return Num(Math.pow(fa, fb), true);
          case '^': if (!fl) { if (neg(b)) { if (a.v === 1) return Int(1); if (a.v === -1) return Int(big(b) % 2n ? -1 : 1); throw evalErr('undefined'); } return Int(big(a) ** big(b)); } return Num(Math.pow(fa, fb), true);
          case 'atan2': case 'atan': return Num(Math.atan2(fa, fb), true);
          case 'log': return Num(Math.log(fb) / Math.log(fa), true);
          case '>>': needInt(); return Int(big(a) >> big(b));
          case '<<': needInt(); return Int(big(a) << big(b));
          case '/\\': needInt(); return Int(big(a) & big(b));
          case '\\/': needInt(); return Int(big(a) | big(b));
          case 'xor': needInt(); return Int(big(a) ^ big(b));
          case 'gcd': { needInt(); let x = big(a), y = big(b); if (x < 0n) x = -x; if (y < 0n) y = -y; while (y) { [x, y] = [y, x % y]; } return Int(x); }
          case 'copysign': return Num(Math.sign(fb) * Math.abs(fa), true);
          case 'truncate': break;
          case 'cot': break;
          case 'random_between': break;
        }
        throw typeError('evaluable', Cmp('/', [Atom(t.f), Int(t.a.length)]));
      }
    }
    throw typeError('evaluable', t);
  }
  function compareNum(a, b) { return a.v < b.v ? -1 : a.v > b.v ? 1 : 0; } // < and > compare a BigInt and a number exactly
  const toBig = x => { if (!isFinite(x)) throw evalErr('undefined'); return BigInt(x); };
  const roundBig = x => toBig(x < 0 ? -Math.round(-x) : Math.round(x));
  const floorDiv = (x, y) => { const q = x / y; return (x % y !== 0n) && ((x < 0n) !== (y < 0n)) ? q - 1n : q; };
  const now = (typeof performance !== 'undefined' && performance.now) ? () => performance.now() : () => Date.now();

  // ---------- text helpers ----------
  function textOf(t, what) {
    t = deref(t);
    switch (t.t) {
      case 'a': return t.n;
      case 's': return t.v;
      case 'n': return P.show(t);
      case 'v': throw instErr();
      case 'c': {
        const arr = listToArray(t);
        if (arr) {
          let s = '';
          for (let x of arr) { x = deref(x); if (x.t === 'n') s += String.fromCodePoint(x.v); else if (x.t === 'a') s += x.n; else if (x.t === 'v') throw instErr(); else throw typeError(what || 'text', t); }
          return s;
        }
      }
    }
    throw typeError(what || 'text', t);
  }
  function parseNumber(s) {
    const st = s.trim();
    if (!/^[+-]?(\d[\d_]*(\.\d+)?([eE][+-]?\d+)?|0x[0-9a-fA-F]+|0'.)$/.test(st) && !/^[+-]?(inf|nan)$/.test(st)) return null;
    try { const c = P.readTerm(st); const t = deref(c.term); if (t.t === 'n') return t; if (t.t === 'c' && t.f === '-' && t.a.length === 1 && deref(t.a[0]).t === 'n') { const x = deref(t.a[0]); return Num(-x.v, x.f); } if (t.t === 'c' && t.f === '+' && t.a.length === 1) return deref(t.a[0]); } catch (e) { }
    return null;
  }
  const charsList = s => list([...s].map(c => Atom(c)));
  const codesList = s => list([...s].map(c => Int(c.codePointAt(0))));

  // format/2 directives
  function format(fmt, argsT) {
    const f = textOf(fmt);
    let args = listToArray(argsT); if (!args) args = [argsT];
    let out = ''; let ai = 0; let lastCol = 0; const fills = [];
    const nextArg = () => { if (ai >= args.length) throw new PlError(Cmp('error', [Cmp('format', [Str('not enough arguments')]), Var()])); return args[ai++]; };
    for (let i = 0; i < f.length; i++) {
      const c = f[i];
      if (c !== '~') { out += c; continue; }
      i++; let num = '';
      while (i < f.length && /[0-9*]/.test(f[i])) { if (f[i] === '*') num += deref(nextArg()).v; else num += f[i]; i++; }
      if (f[i] === '`') { num = String(f[i + 1].codePointAt(0)); i += 2; }
      const d = f[i]; const n = num === '' ? null : parseInt(num, 10);
      switch (d) {
        case 'w': out += show(nextArg(), { quoted: false, swi: !!P.SWI_WRITE }); break;
        case 'p': out += show(nextArg(), { quoted: !!P.SWI_WRITE, swi: !!P.SWI_WRITE }); break;
        case 'q': out += show(nextArg(), { quoted: true, swi: !!P.SWI_WRITE }); break;
        case 'a': out += textOf(nextArg()); break;
        case 'd': { const x = deref(nextArg()); if (x.t !== 'n' || x.f) throw typeError('integer', x); if (n) { const s = String(x.v < 0 ? -x.v : x.v).padStart(n + 1, '0'); out += (x.v < 0 ? '-' : '') + s.slice(0, s.length - n) + '.' + s.slice(s.length - n); } else out += String(x.v); break; }
        case 'D': { const x = deref(nextArg()); out += String(x.v).replace(/\B(?=(\d{3})+(?!\d))/g, ','); break; }
        case 'f': case 'e': case 'g': { const x = evalArith(nextArg()); const v = Number(x.v); out += d === 'f' ? v.toFixed(n === null ? 6 : n) : d === 'e' ? v.toExponential(n === null ? 6 : n).replace(/e([+-])(\d)$/, 'e$10$2') : String(v); break; }
        case 'W': { const t = nextArg(), o = P.listToArray(nextArg()) || []; const has = (f, v) => o.some((x) => { x = deref(x); return x.t === 'c' && x.f === f && deref(x.a[0]).n === v; }); out += show(t, { quoted: has('quoted', 'true'), swi: !!P.SWI_WRITE, nextArg: has('spacing', 'next_argument') }); break; }
        case 's': out += textOf(nextArg()); break;
        case 'n': out += '\n'.repeat(n || 1); break;
        case 'c': { const x = deref(nextArg()); out += String.fromCodePoint(x.v).repeat(n || 1); break; }
        case 'r': { const x = deref(nextArg()); out += x.v.toString(n || 8); break; }
        case '~': out += '~'; break;
        case 't': fills.push(out.length); break;
        case '|': case '+': {
          const lineStart = out.lastIndexOf('\n') + 1;
          const colStart = Math.max(lineStart, lastCol);
          const target = d === '+' ? colStart + (n === null ? 8 : n) : lineStart + (n === null ? out.length - lineStart : n);
          const seg = out.slice(colStart); const pad = target - out.length;
          if (pad > 0) { if (fills.length) { const at = fills[fills.length - 1]; out = out.slice(0, at) + ' '.repeat(pad) + out.slice(at); } else if (d === '+') out = out.slice(0, colStart) + ' '.repeat(pad) + seg; else out += ' '.repeat(pad); }
          fills.length = 0; lastCol = out.length; break;
        }
        case 'i': nextArg(); break;
        default: out += '~' + d;
      }
    }
    return out;
  }

  // ---------- engine ----------
  const CONTROL = new Set([',/2', ';/2', '->/2', '*->/2', '!/0', 'true/0', 'fail/0', 'false/0', 'call/1', '\\+/1', 'not/1', 'findall/3', 'findall/4', 'forall/2', 'once/1', 'ignore/1', 'catch/3', 'throw/1', 'bagof/3', 'setof/3', 'aggregate_all/3', 'aggregate_all/4']);

  function Engine(prog, opts) {
    this.prog = prog; opts = opts || {};
    this.trail = [];
    this.steps = 0; this.cpCreated = 0; this.maxCP = 0; this.out = '';
    this.stepLimit = opts.stepLimit || 5e6;
    this.globals = new Map();
    this.onOut = opts.onOut || null;
    // SWI-Prolog's I/O (src/swi.js): io = { out(s), err(s), readFile(p), writeFile(p, s, append), stat(p), list(p), stdin, argv, cwd }
    this.accel = opts.accel || null;
    this.io = opts.io || null; this.err = ''; this.onErr = opts.onErr || null; this.streams = new Map(); this.streamSeq = 0;
    this.flags = { occurs_check: false };
    this.depth = 0;
  }
  Engine.prototype.bind = function (v, t) { v.ref = t; this.trail.push(v); };
  Engine.prototype.undo = function (mark) { const tr = this.trail; while (tr.length > mark) tr.pop().ref = null; };
  Engine.prototype.unify = function (a, b) {
    const st = [a, b];
    while (st.length) {
      let y = deref(st.pop()), x = deref(st.pop());
      if (x === y) continue;
      if (x.t === 'v') { this.bind(x, y); continue; }
      if (y.t === 'v') { this.bind(y, x); continue; }
      if (x.t !== y.t) return false;
      switch (x.t) {
        case 'a': return false;
        case 'n': if (x.v !== y.v || x.f !== y.f) return false; continue;
        case 's': if (x.v !== y.v) return false; continue;
        case 'c':
          if (x.f !== y.f || x.a.length !== y.a.length) return false;
          for (let i = 0; i < x.a.length; i++) { st.push(x.a[i], y.a[i]); }
          continue;
      }
    }
    return true;
  };
  Engine.prototype.write = function (s) { this.out += s; if (this.onOut) this.onOut(s); };
  Engine.prototype.writeErr = function (s) { this.err += s; if (this.onErr) this.onErr(s); };

  // solve goal; calls onSol() for each solution; onSol returns true to continue.
  Engine.prototype.solve = function (goal, onSol, depthCut) {
    this.depth++;
    if (this.depth > 400) { this.depth--; throw new LimitError('nesting limit (findall/\\+/call depth) exceeded'); }
    try { return this._run(goal, onSol); } finally { this.depth--; }
  };
  Engine.prototype._run = function (goal, onSol) {
    const self = this;
    const cps = [];
    let goals = { g: goal, cb: 0, next: null };
    const base = 0;
    const builtins = P.builtins;
    const push = cp => { cps.push(cp); self.cpCreated++; if (cps.length > self.maxCP) self.maxCP = cps.length; };
    let stopped = false;
    const backtrack = () => {
      for (;;) {
        if (cps.length === base) return false;
        const cp = cps[cps.length - 1];
        self.undo(cp.trail);
        if (cp.kind === 'alt') { cps.pop(); goals = cp.goals; return true; }
        if (cp.kind === 'clauses') {
          const res = self.tryClauses(cp.goal, cp.clauses, cp.idx, cp.next, cp.cb, cps, cp);
          if (res) { goals = res; return true; }
          continue;
        }
        if (cp.kind === 'gen') {
          const r = cp.it.next();
          if (!r.done) { goals = cp.next; return true; }
          cps.pop(); continue;
        }
        if (cp.kind === 'barrier' || cp.kind === 'catch') { cps.pop(); continue; }
        cps.pop();
      }
    };
    for (;;) {
      if (goals === null) {
        const more = onSol();
        if (!more) { stopped = true; return true; }
        if (!backtrack()) return false;
        continue;
      }
      const fr = goals; goals = fr.next;
      let g = deref(fr.g);
      if (++self.steps > self.stepLimit) throw new LimitError('step limit (' + self.stepLimit + ') exceeded');
      try {
        if (g.t === 'v') throw instErr();
        let f, n, a;
        if (g.t === 'a') { f = g.n; n = 0; a = []; }
        else if (g.t === 'c') { f = g.f; n = g.a.length; a = g.a; }
        else throw typeError('callable', g);
        const k = f + '/' + n;
        switch (k) {
          case 'true/0': continue;
          case 'fail/0': case 'false/0': if (!backtrack()) return false; continue;
          case ',/2': self.steps--; goals = { g: a[0], cb: fr.cb, next: { g: a[1], cb: fr.cb, next: goals } }; continue;
          case '!/0': cps.length = Math.max(fr.cb, base); continue;
          case ';/2': {
            const l = deref(a[0]);
            if (l.t === 'c' && l.f === '->' && l.a.length === 2) {
              const B = cps.length;
              push({ kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.trail.length });
              goals = { g: l.a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: l.a[1], cb: fr.cb, next: goals } } };
              continue;
            }
            if (l.t === 'c' && l.f === '*->' && l.a.length === 2) {
              const alt = { kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.trail.length };
              push(alt);
              goals = { g: l.a[0], cb: cps.length, next: { g: Cmp('$softcut', [{ t: 'n', v: 0, cp: alt }]), cb: fr.cb, next: { g: l.a[1], cb: fr.cb, next: goals } } };
              continue;
            }
            push({ kind: 'alt', goals: { g: a[1], cb: fr.cb, next: goals }, trail: self.trail.length });
            goals = { g: a[0], cb: fr.cb, next: goals };
            continue;
          }
          case '->/2': {
            const B = cps.length;
            push({ kind: 'barrier', trail: self.trail.length });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: a[1], cb: fr.cb, next: goals } } };
            continue;
          }
          case '*->/2': goals = { g: a[0], cb: cps.length, next: { g: a[1], cb: fr.cb, next: goals } }; continue;
          case '$ite/1': cps.length = deref(a[0]).v; continue;
          case '$softcut/1': { const alt = a[0].cp; const i = cps.indexOf(alt); if (i >= 0) cps[i] = { kind: 'barrier', trail: alt.trail }; continue; }
          case '\\+/1': case 'not/1': {
            const B = cps.length;
            push({ kind: 'alt', goals: goals, trail: self.trail.length });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: { g: P.FAIL, cb: fr.cb, next: null } } };
            continue;
          }
          case 'call/1': goals = { g: a[0], cb: cps.length, next: goals }; continue;
          case 'once/1': {
            const B = cps.length;
            push({ kind: 'barrier', trail: self.trail.length });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: goals } };
            continue;
          }
          case 'ignore/1': {
            const B = cps.length;
            push({ kind: 'alt', goals: goals, trail: self.trail.length });
            goals = { g: a[0], cb: cps.length, next: { g: Cmp('$ite', [Int(B)]), cb: fr.cb, next: goals } };
            continue;
          }
          case 'forall/2': {
            let ok = true; const mark = self.trail.length;
            self.solve(a[0], () => { let s = false; const m2 = self.trail.length; self.solve(a[1], () => { s = true; return false; }); self.undo(m2); if (!s) { ok = false; return false; } return true; });
            self.undo(mark);
            if (!ok && !backtrack()) return false; continue;
          }
          case 'findall/3': case 'findall/4': {
            const res = []; const mark = self.trail.length;
            self.solve(a[1], () => { res.push(copy(a[0])); return true; });
            self.undo(mark);
            if (!self.unify(a[2], list(res, n === 4 ? a[3] : NIL))) { if (!backtrack()) return false; }
            continue;
          }
          case 'bagof/3': case 'setof/3': {
            // grouping by free variables (^ supported)
            let gl = deref(a[1]); const exVars = [];
            while (gl.t === 'c' && gl.f === '^' && gl.a.length === 2) { termVars(gl.a[0], exVars); gl = deref(gl.a[1]); }
            const tv = termVars(a[0]); const ex = new Set(tv.concat(exVars));
            const free = termVars(gl).filter(v => !ex.has(v));
            const W = list(free);
            const res = []; const mark = self.trail.length;
            self.solve(gl, () => { res.push(copy(Cmp('-', [W, a[0]]))); return true; });
            self.undo(mark);
            if (!res.length) { if (!backtrack()) return false; continue; }
            // group
            const groups = [];
            if (free.length === 0) groups.push({ w: W, items: res.map(r => r.a[1]) });
            else {
              const sorted = k === 'setof/3' ? res.slice().sort((x, y) => compare(x.a[0], y.a[0])) : res.slice().sort((x, y) => compare(x.a[0], y.a[0]));
              for (const r of sorted) { const gq = groups.find(gq => P.variantKey(gq.w) === P.variantKey(r.a[0])); if (gq) gq.items.push(r.a[1]); else groups.push({ w: r.a[0], items: [r.a[1]] }); }
            }
            const alts = groups.map(gq => {
              let items = gq.items;
              if (k === 'setof/3') items = sortUnique(items);
              return Cmp(',', [Cmp('=', [W, gq.w]), Cmp('=', [a[2], list(items)])]);
            });
            goals = { g: disj(alts), cb: fr.cb, next: goals };
            continue;
          }
          case 'aggregate_all/3': {
            const spec = deref(a[0]); const res = []; const mark = self.trail.length;
            const sk = P.key(spec);
            const tmpl = sk === 'count/0' ? P.TRUE : spec.t === 'c' ? spec.a[0] : P.TRUE;
            self.solve(a[1], () => { res.push(copy(tmpl)); return true; });
            self.undo(mark);
            let r;
            switch (sk) {
              case 'count/0': r = Int(res.length); break;
              case 'count/1': r = Int(res.length); break;
              case 'sum/1': { let s = Int(0); for (const x of res) s = evalArith(Cmp('+', [s, x])); r = s; break; }
              case 'max/1': if (!res.length) { r = null; break; } r = res.map(evalArith).reduce((m, x) => x.v > m.v ? x : m); break;
              case 'min/1': if (!res.length) { r = null; break; } r = res.map(evalArith).reduce((m, x) => x.v < m.v ? x : m); break;
              case 'bag/1': r = list(res); break;
              case 'set/1': r = list(sortUnique(res)); break;
              default: throw typeError('aggregate_spec', spec);
            }
            if (r === null || !self.unify(a[2], r)) { if (!backtrack()) return false; }
            continue;
          }
          case 'catch/3': {
            push({ kind: 'catch', catcher: a[1], recovery: a[2], next: goals, cb: fr.cb, trail: self.trail.length });
            goals = { g: a[0], cb: cps.length, next: goals };
            continue;
          }
          case 'throw/1': throw new PlError(copy(a[0]));
          case 'with_output_to/2': {
            const save = self.out; self.out = ''; let ok = false; const mark = self.trail.length;
            try { self.solve(a[1], () => { ok = true; return false; }); } finally { var txt = self.out; self.out = save; }
            const sk = deref(a[0]);
            if (!ok) { self.undo(mark); if (!backtrack()) return false; continue; }
            const v = sk.f === 'atom' ? Atom(txt) : sk.f === 'string' ? Str(txt) : sk.f === 'codes' ? P.codesList(txt) : P.charsList(txt);
            if (!self.unify(sk.a[0], v)) { if (!backtrack()) return false; }
            continue;
          }
        }
        if (k.startsWith('call/') && n > 1) {
          const c = deref(a[0]); const extra = a.slice(1);
          let ng;
          const cq = c.t === 'c' && c.f === ':' && c.a.length === 2 ? deref(c.a[1]) : null; // call(M:G, X): M:G(X)
          if (cq) ng = Cmp(':', [c.a[0], cq.t === 'a' ? Cmp(cq.n, extra) : cq.t === 'c' ? Cmp(cq.f, cq.a.concat(extra)) : Cmp('call', [cq].concat(extra))]);
          else if (c.t === 'a') ng = Cmp(c.n, extra); else if (c.t === 'c') ng = Cmp(c.f, c.a.concat(extra)); else if (c.t === 'v') throw instErr(); else throw typeError('callable', c);
          goals = { g: ng, cb: cps.length, next: goals };
          continue;
        }
        const clauses = self.prog.preds.get(k);
        // a faster route for this call (the interpreter's: src/interp.js), as a generator of its answers
        if (clauses && self.accel) {
          const it = self.accel(k, g, self);
          if (it) {
            const mark = self.trail.length;
            const r = it.next();
            if (r.done) { self.undo(mark); if (!backtrack()) return false; continue; }
            if (r.value !== 'last') push({ kind: 'gen', it, next: goals, trail: mark });
            continue;
          }
        }
        if (clauses) {
          const res = self.tryClauses(g, clauses, 0, goals, null, cps, null, push);
          if (res) { goals = res; continue; }
          if (!backtrack()) return false;
          continue;
        }
        const bi = builtins[k];
        if (bi) {
          if (bi.nondet) {
            const it = bi.fn(a, self, g);
            const mark = self.trail.length;
            const r = it.next();
            if (r.done) { self.undo(mark); if (!backtrack()) return false; continue; }
            if (r.value === 'last') continue; // deterministic exit
            push({ kind: 'gen', it, next: goals, trail: mark });
            continue;
          }
          if (bi.call) { // builtin that expands into a goal
            const ng = bi.fn(a, self, g);
            if (ng === null) { if (!backtrack()) return false; continue; }
            goals = { g: ng, cb: cps.length, next: goals };
            continue;
          }
          const mark = self.trail.length;
          if (!bi.fn(a, self, g)) { self.undo(mark); if (!backtrack()) return false; }
          continue;
        }
        if (self.prog.dynamic.has(k)) { if (!backtrack()) return false; continue; }
        // a goal built at run time that names a module's private predicate (src/swi.js)
        if (self.prog.privates && self.prog.privates.has(k)) { const nm = self.prog.privates.get(k)[0]; goals = { g: g.t === 'a' ? Atom(nm) : Cmp(nm, a), cb: cps.length, next: goals }; continue; }
        throw existErr(k);
      } catch (e) {
        if (!(e instanceof PlError)) throw e;
        // find catch frame
        let handled = false;
        while (cps.length > base) {
          const cp = cps.pop();
          if (cp.kind === 'catch') {
            self.undo(cp.trail);
            const mark = self.trail.length;
            const ball = copy(e.term);
            if (self.unify(cp.catcher, ball)) { goals = { g: cp.recovery, cb: cp.cb, next: cp.next }; handled = true; break; }
            self.undo(mark);
          }
        }
        if (!handled) throw e;
      }
    }
  };
  function disj(alts) { if (!alts.length) return P.FAIL; let r = alts[alts.length - 1]; for (let i = alts.length - 2; i >= 0; i--) r = Cmp(';', [alts[i], r]); return r; }
  function sortUnique(items) { const s = items.slice().sort(compare); const out = []; for (const x of s) if (!out.length || compare(out[out.length - 1], x) !== 0) out.push(x); return out; }

  // first-argument indexing compatible?
  function firstArgMayMatch(goalArg, headArg) {
    const g = deref(goalArg), h = deref(headArg);
    if (g.t === 'v' || h.t === 'v') return true;
    if (g.t !== h.t) return false;
    if (g.t === 'a') return g.n === h.n;
    if (g.t === 'n') return g.v === h.v;
    if (g.t === 's') return g.v === h.v;
    return g.f === h.f && g.a.length === h.a.length;
  }
  Engine.prototype.tryClauses = function (g, clauses, start, next, cbIn, cps, cp, push) {
    const self = this;
    const ga = g.t === 'c' ? g.a : null;
    const fa = ga ? ga[0] : null;
    // find first candidate from start
    let i = start;
    const cand = j => !fa || firstArgMayMatch(fa, clauses[j].head.a[0]);
    while (i < clauses.length && !cand(i)) i++;
    if (i >= clauses.length) { if (cp) cps.pop(); return null; }
    for (;;) {
      let j = i + 1; while (j < clauses.length && !cand(j)) j++;
      const hasMore = j < clauses.length;
      const cb = cp ? cp.cb : cps.length;
      if (cp) { if (hasMore) { cp.idx = j; } else cps.pop(); }
      else if (hasMore) { cp = { kind: 'clauses', goal: g, clauses, idx: j, next, cb, trail: self.trail.length }; push(cp); }
      const cl = clauses[i];
      const m = new Map();
      const h = copy(cl.head, m);
      const mark = self.trail.length;
      if (self.unify(h, g)) {
        const body = deref(cl.body);
        if (body.t === 'a' && body.n === 'true') return next === null ? { g: P.TRUE, cb, next: null } : next;
        return { g: copy(body, m), cb, next };
      }
      self.undo(mark);
      if (!hasMore) return null;
      i = j;
      if (cp && cps[cps.length - 1] !== cp) return null;
    }
  };

  // ---------- running queries ----------
  // returns { ok, answers:[{text, bindings}], events:[{k:'row'|'out', text}], output, steps, cps, maxCP, timeMs, error }
  function runQuery(prog, queryText, opts) {
    opts = opts || {};
    if (typeof prog === 'string') prog = loadProgram(prog);
    const q = typeof queryText === 'string' ? P.readTerm(queryText) : queryText;
    if (P.expandDots && P.hasDots(q.term)) q.term = P.expandDots(Cmp(':-', [Atom('$q'), q.term])).a[1];
    const vars = q.vars.filter(([nm]) => !nm.startsWith('_'));
    const eng = new Engine(prog, opts);
    const maxAnswers = opts.maxAnswers || 1000;
    const answers = [], events = [];
    let lastOut = 0, error = null, limit = false, halted = null;
    const t0 = now();
    try {
      runInitGlobals(eng, prog);
      eng.solve(q.term, () => {
        if (eng.out.length > lastOut) { events.push({ k: 'out', text: eng.out.slice(lastOut) }); lastOut = eng.out.length; }
        const nm = P.namer();
        const text = vars.length ? vars.map(([n, v]) => n + ' = ' + show(v, { varName: nm })).join(', ') : 'true';
        answers.push({ text }); events.push({ k: 'row', text });
        return answers.length < maxAnswers;
      });
    } catch (e) { if (e && e.halt) { halted = e.code; } else error = e.limit ? e.message : e.prolog ? (e.term ? errText(e.term) : e.message) : e.message; limit = !!e.limit; if (!e.prolog && !e.limit && opts.debug) console.error(e); }
    const t1 = now();
    eng.undo(0); // leave the (possibly reused) query term unbound
    if (eng.out.length > lastOut) events.push({ k: 'out', text: eng.out.slice(lastOut) });
    if (P.closeStreams) P.closeStreams(eng);
    return { ok: !error, answers, events, output: eng.out, errOutput: eng.err, halted, steps: eng.steps, cps: eng.cpCreated, maxCP: eng.maxCP, timeMs: t1 - t0, error, limit, truncated: answers.length >= maxAnswers };
  }
  function runInitGlobals() { }
  function errText(t) { t = deref(t); if (t.t === 'c' && t.f === 'error' && t.a.length === 2) return show(t.a[0], { varName: P.namer() }); return 'uncaught ' + show(t, { varName: P.namer() }); }
  P.errText = errText;

  Object.assign(P, { Engine, Program, loadProgram, runQuery, evalArith, textOf, parseNumber, charsList, codesList, format, PlError, LimitError, typeError, instErr, commaList, CONTROL, now, sortUnique, disj, firstArgMayMatch, dcgTransform });
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
