/* thermo.js - the thermodynamic compression MNN of mnns (prolog/thermo/thermo.pl), in JavaScript,
   and a lossless store for data the interpreter keeps (src/interp.js).

   A sequence is coded as { alphabet, counts, rank }: its sorted distinct symbols, how often each
   occurs, and its rank, from 0, among all sequences with exactly those counts in dictionary order
   (enumerative coding). For length N and counts c1..ck there are M = N! / (c1! ... ck!) such
   sequences and their ranks are exactly 0..M-1, so the rank needs ceil(log2 M) bits; no code that
   tells them apart can use fewer (pigeonhole), and log2 M =< N * H(counts).

   The rank is a sum of one neuron per position: with M and N for the counts still left, a position
   holding the I-th symbol fires with weight M * (c1 + ... + c(I-1)) / N. Each M * cj / N is the
   multinomial with cj lowered by one (Pascal's rule), a whole number, and the k blocks of sizes
   M * cj / N tile 0..M-1. Decoding finds the block that holds the rank: with q = floor(R * N / M),
   R lies in block j exactly when P_j =< q < P_(j+1) (P the prefix sums of the counts), because
   R * N < M * P <=> q < P for whole P. So each position costs a few multiplies and divides.

   The coder is a bijection on the class, so it erases nothing (Landauer: no heat needed).

   pack(text) stores a string in blocks of symbols (UTF-16 code units), each block as a bitmap of
   the symbols it uses, their counts (Elias gamma) and its rank in exactly ceil(log2 M) bits. */
(function (P) {
  'use strict';
  const big = BigInt;
  const sortSyms = (xs) => [...new Set(xs)].sort((a, b) => (typeof a === 'number' && typeof b === 'number' ? a - b : String(a) < String(b) ? -1 : String(a) > String(b) ? 1 : 0));

  function multinomial(counts) {
    // N! / prod ci!, built as a product of binomials so that every step is whole
    let m = 1n, n = 0;
    for (const c of counts) for (let i = 1; i <= c; i++) { n++; m = m * big(n) / big(i); }
    return m;
  }
  const bitsFor = (v) => (v <= 1n ? 0 : (v - 1n).toString(2).length);
  function compositions(n, k) { if (k === 0) return n === 0 ? 1n : 0n; let c = 1n; for (let i = 1; i <= k - 1; i++) c = c * big(n + i) / big(i); return c; }

  function compress(seq) {
    const alphabet = sortSyms(seq), idx = new Map(alphabet.map((a, i) => [a, i]));
    const counts = alphabet.map(() => 0); for (const x of seq) counts[idx.get(x)]++;
    return { alphabet, counts: counts.slice(), rank: rankOf(seq.map((x) => idx.get(x)), counts) };
  }
  // rank of a sequence of symbol indices with the given counts (counts are used up)
  function rankOf(ix, counts0) {
    const counts = counts0.slice(); let n = ix.length, m = multinomial(counts), r = 0n;
    for (const i of ix) {
      let pre = 0; for (let j = 0; j < i; j++) pre += counts[j];
      const N = big(n);
      r += m * big(pre) / N;
      m = m * big(counts[i]) / N; counts[i]--; n--;
    }
    return r;
  }
  // the sequence of symbol indices with these counts and rank (null if the rank is out of range)
  function unrankOf(counts0, rank) {
    const counts = counts0.slice(); let n = counts.reduce((a, b) => a + b, 0), m = multinomial(counts), r = rank;
    if (r < 0n || r >= m) return null;
    const out = new Array(n);
    for (let p = 0; n > 0; p++) {
      const N = big(n), q = Number(r * N / m);
      let j = 0, pre = 0; while (pre + counts[j] <= q) { pre += counts[j]; j++; }
      r -= m * big(pre) / N;
      m = m * big(counts[j]) / N; counts[j]--; n--;
      out[p] = j;
    }
    return r === 0n ? out : null;
  }
  function decompress(code) {
    const { alphabet, counts, rank } = code;
    if (!Array.isArray(alphabet) || !Array.isArray(counts) || alphabet.length !== counts.length) return null;
    if (counts.some((c) => !Number.isInteger(c) || c < 0)) return null;
    const ix = unrankOf(counts, big(rank)); return ix && ix.map((i) => alphabet[i]);
  }
  function neurons(seq) {
    const alphabet = sortSyms(seq), idx = new Map(alphabet.map((a, i) => [a, i]));
    const counts = alphabet.map(() => 0); for (const x of seq) counts[idx.get(x)]++;
    let n = seq.length, m = multinomial(counts); const out = [];
    seq.forEach((x, p) => { const i = idx.get(x); let pre = 0; for (let j = 0; j < i; j++) pre += counts[j]; const N = big(n); out.push({ position: p + 1, symbol: x, weight: m * big(pre) / N }); m = m * big(counts[i]) / N; counts[i]--; n--; });
    return out;
  }
  const KB = 1.380649e-23;
  const sig4 = (x) => Number(x.toExponential(3));
  const landauer = (bits, kelvin) => sig4(bits * KB * kelvin * Math.log(2));
  const entropyExact = (counts, n) => (n === 0 ? 0 : counts.reduce((h, c) => (c ? h - (c * Math.log(c / n)) / Math.log(2) : h), 0));
  function report(seq) {
    const { alphabet, counts, rank } = compress(seq), n = seq.length, k = alphabet.length, m = multinomial(counts);
    const rb = bitsFor(m), cb = bitsFor(compositions(n, k)), raw = n * bitsFor(big(k));
    const erased = Math.max(0, raw - rb - cb);
    return { n, alphabet, counts, rank, classSize: m, rankBits: rb, compositionBits: cb, rawBits: raw, entropyBits: Math.round(entropyExact(counts, n) * 1000) / 1000, erasedBitsIrreversible: erased, erasedBitsReversible: 0, landauerJoules300K: landauer(erased, 300) };
  }

  // The checks of thermo_prove/3 on every sequence over the alphabet up to maxLen (=< 8):
  // round trip, ranks of each class exactly 0..M-1, neuron sum, entropy bound, no erasure.
  function prove(alphabet0, maxLen) {
    const alphabet = sortSyms(alphabet0);
    if (alphabet.length !== alphabet0.length || alphabet.length < 1 || alphabet.length > 4 || !(maxLen >= 0 && maxLen <= 8)) return { rejected: 'bad_domain' };
    const seqs = []; (function gen(s) { seqs.push(s); if (s.length < maxLen) for (const a of alphabet) gen(s.concat([a])); })([]);
    const classes = new Map();
    for (const s of seqs) {
      const c = compress(s); const back = decompress(c);
      if (!back || back.length !== s.length || back.some((x, i) => x !== s[i])) return { rejected: 'round_trip', witness: s };
      if (neurons(s).reduce((a, x) => a + x.weight, 0n) !== c.rank) return { rejected: 'neuron_sum', witness: s };
      const r = report(s); if (r.rankBits > Math.ceil(entropyExact(r.counts, r.n) - 1e-9)) return { rejected: 'entropy_bound', witness: s };
      const key = JSON.stringify([c.alphabet, c.counts]); if (!classes.has(key)) classes.set(key, []); classes.get(key).push(c.rank);
    }
    for (const [key, rs] of classes) {
      const m = multinomial(JSON.parse(key)[1]); rs.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
      if (big(rs.length) !== m || rs.some((r, i) => r !== big(i))) return { rejected: 'bijection', witness: JSON.parse(key) };
    }
    return { proof: [
      { step: 1, name: 'thermo_round_trip', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 2, name: 'thermo_bijection', verified: { typeClasses: classes.size, ranks: 'exact' } },
      { step: 3, name: 'thermo_neuron_sum', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 4, name: 'thermo_entropy_bound', verified: { domain: [alphabet, maxLen], count: seqs.length } },
      { step: 5, name: 'thermo_landauer', erasedBits: 0 }] };
  }

  // ---- the store: a string as blocks of thermo codes, in a byte array ----
  class BitW {
    constructor() { this.bytes = []; this.cur = 0; this.n = 0; }
    bit(b) { this.cur = (this.cur << 1) | b; if (++this.n === 8) { this.bytes.push(this.cur); this.cur = 0; this.n = 0; } }
    bits(v, w) { for (let i = w - 1; i >= 0; i--) this.bit((v >>> i) & 1); }
    bigBits(v, w) { const s = v.toString(2).padStart(w, '0'); for (let i = 0; i < w; i++) this.bit(s.charCodeAt(i) & 1); }
    gamma(v) { const w = v.toString(2).length; for (let i = 1; i < w; i++) this.bit(0); this.bits(v, w); } // v >= 1
    done() { if (this.n) { this.bytes.push(this.cur << (8 - this.n)); } return Uint8Array.from(this.bytes); }
  }
  class BitR {
    constructor(u8, pos) { this.u = u8; this.p = pos * 8; }
    bit() { const b = (this.u[this.p >> 3] >> (7 - (this.p & 7))) & 1; this.p++; return b; }
    bits(w) { let v = 0; for (let i = 0; i < w; i++) v = (v << 1) | this.bit(); return v >>> 0; }
    bigBits(w) { if (!w) return 0n; let s = ''; for (let i = 0; i < w; i++) s += this.bit(); return BigInt('0b' + s); }
    gamma() { let z = 0; while (!this.bit()) z++; let v = 1; for (let i = 0; i < z; i++) v = (v << 1) | this.bit(); return v; }
  }
  const MAGIC = [0x54, 0x48, 0x31]; // "TH1"
  function pack(text, { block = 128 } = {}) {
    const units = []; for (let i = 0; i < text.length; i++) units.push(text.charCodeAt(i));
    const alphabet = sortSyms(units), idx = new Map(alphabet.map((a, i) => [a, i]));
    const w = new BitW();
    MAGIC.forEach((b) => w.bits(b, 8));
    w.gamma(alphabet.length + 1); for (const a of alphabet) w.bits(a, 16);
    w.gamma(block); w.gamma(units.length + 1);
    for (let s = 0; s < units.length; s += block) {
      const ix = units.slice(s, s + block).map((u) => idx.get(u));
      const counts = alphabet.map(() => 0); for (const i of ix) counts[i]++;
      for (const c of counts) w.bit(c ? 1 : 0);
      for (const c of counts) if (c) w.gamma(c);
      const used = counts.filter((c) => c), local = []; const map = []; counts.forEach((c, i) => { if (c) { map[i] = local.length; local.push(i); } });
      const m = multinomial(used);
      w.bigBits(rankOf(ix.map((i) => map[i]), used), bitsFor(m));
    }
    return w.done();
  }
  function unpack(u8) {
    if (!u8 || u8.length < 3 || u8[0] !== MAGIC[0] || u8[1] !== MAGIC[1] || u8[2] !== MAGIC[2]) throw new Error('not a thermo store');
    const r = new BitR(u8, 3);
    const k = r.gamma() - 1, alphabet = []; for (let i = 0; i < k; i++) alphabet.push(r.bits(16));
    const block = r.gamma(), total = r.gamma() - 1;
    const parts = [];
    for (let s = 0; s < total; s += block) {
      const present = alphabet.map(() => r.bit());
      const used = [], local = []; present.forEach((b, i) => { if (b) { used.push(r.gamma()); local.push(alphabet[i]); } });
      const m = multinomial(used);
      const ix = unrankOf(used, r.bigBits(bitsFor(m))); if (!ix) throw new Error('corrupt thermo store');
      parts.push(String.fromCharCode(...ix.map((i) => local[i])));
    }
    const out = parts.join(''); if (out.length !== total) throw new Error('corrupt thermo store');
    return out;
  }
  const toBase64 = (u8) => (typeof Buffer !== 'undefined' ? Buffer.from(u8).toString('base64') : btoa(String.fromCharCode(...u8)));
  const fromBase64 = (s) => (typeof Buffer !== 'undefined' ? new Uint8Array(Buffer.from(s, 'base64')) : Uint8Array.from(atob(s), (c) => c.charCodeAt(0)));

  P.thermo = { compress, decompress, neurons, report, prove, landauer, multinomial, pack, unpack, toBase64, fromBase64 };
})(typeof module !== 'undefined' && module.exports ? (globalThis.PL2D = globalThis.PL2D || {}) : (window.PL2D = window.PL2D || {}));
