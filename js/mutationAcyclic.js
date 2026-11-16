/*
 * mutationAcyclic.js -- decide whether a quiver is mutation-acyclic, with exact arithmetic and guaranteed termination.
 *
 * A line-by-line port of quiver-mutation/mutation_acyclic.py (the bounded axis walk of the accompanying write-up,
 * Section 6, Algorithm 4' and the implemented variant). Every number in the decision logic is a BigInt or a rational
 * built from BigInts; there is no floating point. Real algebraic numbers rho are integer polynomials with a dyadic
 * isolating interval; signs are decided by interval evaluation with an exact zero test (gcd with the defining
 * polynomial).
 *
 * The default mode orders 'auto' is the reference's _decide_auto: rigorous NO filters (vortex [Ne, Thm 4.4];
 * mutation-cyclic 3-vertex full subquivers [BBH, BMR]), a combinatorial YES path (unforking + plateau search), then
 * SELECT: one order of Lambda(B) in polynomial time (winding targets solved over Q, Bellman-Ford), the Perron rule for
 * the single sign-passing class O^+ (selection theorem, writeup Section 8), and descents at O^+ only; if SELECT were
 * ever inconclusive, the class search (one order per class of Lambda(B), interleaved descents, n+1 rule) runs as a
 * fallback. Late filters (4-vertex subquivers, Coxeter-polynomial candidates) run after 4000 descent steps, and finite
 * mutation type is settled by a search up to isomorphism. orders 'all' (all n! orders) remains available.
 *
 *   YES answers carry a certificate re-checked by verifyCertificate(): c-vectors satisfying the Speyer-Thomas
 *   conditions (arXiv:1203.0277, Thms 1.4 and 7.2) or an explicit mutation sequence. Every YES also carries an
 *   explicit mutation sequence from the input to an acyclic quiver.
 *   NO answers rest on Theorem D of the write-up and, in the default mode, on the selection theorem (Theorem 1).
 *
 * The order of every computation that refines the isolating interval of rho is the same as in the Python reference
 * (including the spectral cache shared by orders with the same Coxeter polynomial and the comparison sequence of
 * CPython's sort), so the two implementations follow identical paths and produce identical answers, reasons,
 * certificates and scheduler statistics (checked by quiver-mutation/jsport).
 *
 * Works in the browser (global MutationAcyclic), in a Web Worker (MutationAcyclic.workerSource()) and under Node.
 */
(function (root) {
'use strict';

function factory() {
'use strict';

// =====================================================================================================================
// BigInt helpers and rationals
// =====================================================================================================================

function babs(x) { return x < 0n ? -x : x; }
function bsgn(x) { return x > 0n ? 1 : (x < 0n ? -1 : 0); }
function bmax(a, b) { return a >= b ? a : b; }
function bgcd(a, b) {
    if (a < 0n) a = -a;
    if (b < 0n) b = -b;
    if (a === 0n) return b;
    if (b === 0n) return a;
    if ((b & (b - 1n)) === 0n) { const la = a & -a; return la < b ? la : b; }   // b a power of two
    if ((a & (a - 1n)) === 0n) { const lb = b & -b; return lb < a ? lb : a; }
    while (b !== 0n) { const t = a % b; a = b; b = t; }
    return a;
}
function bitLength(x) { return x === 0n ? 0 : (x < 0n ? -x : x).toString(2).length; }
function isqrt(x) {                                   // floor(sqrt(x)), x >= 0
    if (x < 0n) throw new Error('isqrt of negative');
    if (x < 2n) return x;
    let r = 1n << BigInt(Math.ceil(bitLength(x) / 2));
    while (true) { const s = (r + x / r) >> 1n; if (s >= r) break; r = s; }
    while (r * r > x) r -= 1n;
    while ((r + 1n) * (r + 1n) <= x) r += 1n;
    return r;
}
function factorial(n) { let r = 1n; for (let i = 2n; i <= BigInt(n); i++) r *= i; return r; }
function floorDiv(a, b) {                             // floor(a / b) for b > 0
    const q = a / b;
    return (a % b !== 0n && a < 0n) ? q - 1n : q;
}

// Rational number n/d with d > 0 and gcd(n, d) = 1 (always normalized, like Python's Fraction).
class Q {
    constructor(n, d) { this.n = n; this.d = d; }
    toString() { return this.d === 1n ? this.n.toString() : this.n.toString() + '/' + this.d.toString(); }
}
const Q0 = new Q(0n, 1n), Q1 = new Q(1n, 1n);
function qn(n, d) {
    if (d === undefined) return new Q(n, 1n);
    if (d < 0n) { n = -n; d = -d; }
    if (d === 0n) throw new Error('division by zero');
    const g = bgcd(n, d);
    return g === 1n ? new Q(n, d) : new Q(n / g, d / g);
}
function qi(x) { return x instanceof Q ? x : new Q(BigInt(x), 1n); }
function qadd(x, y) { return x.d === y.d ? qn(x.n + y.n, x.d) : qn(x.n * y.d + y.n * x.d, x.d * y.d); }
function qsub(x, y) { return x.d === y.d ? qn(x.n - y.n, x.d) : qn(x.n * y.d - y.n * x.d, x.d * y.d); }
function qmul(x, y) { return qn(x.n * y.n, x.d * y.d); }
function qdiv(x, y) { return qn(x.n * y.d, x.d * y.n); }
// unnormalized variants (value-correct, d > 0 kept), for intermediate values that only enter comparisons
function rmul(x, y) { return new Q(x.n * y.n, x.d * y.d); }
function rdiv(x, y) { return y.n < 0n ? new Q(-x.n * y.d, x.d * -y.n) : new Q(x.n * y.d, x.d * y.n); }
function radd(x, y) { return x.d === y.d ? new Q(x.n + y.n, x.d) : new Q(x.n * y.d + y.n * x.d, x.d * y.d); }
function qneg(x) { return new Q(-x.n, x.d); }
function qabs(x) { return x.n < 0n ? new Q(-x.n, x.d) : x; }
function qcmp(x, y) { const a = x.n * y.d, b = y.n * x.d; return a < b ? -1 : (a > b ? 1 : 0); }
function qlt(x, y) { return qcmp(x, y) < 0; }
function qmaxv(x, y) { return qcmp(y, x) > 0 ? y : x; }   // Python max(x, y): first maximal
function qminv(x, y) { return qcmp(y, x) < 0 ? y : x; }
function qzero(x) { return x.n === 0n; }
function qsign(x) { return bsgn(x.n); }
function qpow(x, e) { return new Q(x.n ** BigInt(e), x.d ** BigInt(e)); }   // stays normalized
function qfloor(x) { return floorDiv(x.n, x.d); }
function qceil(x) { return -floorDiv(-x.n, x.d); }
function qmax4(a, b, c, d) { let m = a; if (qcmp(b, m) > 0) m = b; if (qcmp(c, m) > 0) m = c; if (qcmp(d, m) > 0) m = d; return m; }
function qmin4(a, b, c, d) { let m = a; if (qcmp(b, m) < 0) m = b; if (qcmp(c, m) < 0) m = c; if (qcmp(d, m) < 0) m = d; return m; }

// =====================================================================================================================
// integer matrices
// =====================================================================================================================

function zeros(n, m) { const r = []; for (let i = 0; i < n; i++) r.push(new Array(m === undefined ? n : m).fill(0n)); return r; }
function matMul(A, B) {
    const n = A.length, m = B[0].length, l = B.length, out = [];
    for (let i = 0; i < n; i++) {
        const row = new Array(m), Ai = A[i];
        for (let j = 0; j < m; j++) { let s = 0n; for (let k = 0; k < l; k++) s += Ai[k] * B[k][j]; row[j] = s; }
        out.push(row);
    }
    return out;
}
function transpose(A) {
    if (!A.length) return [];
    const out = [];
    for (let j = 0; j < A[0].length; j++) out.push(A.map(r => r[j]));
    return out;
}
function identity(n) { const I = zeros(n); for (let i = 0; i < n; i++) I[i][i] = 1n; return I; }
function negMat(A) { return A.map(r => r.map(x => -x)); }
function matEq(A, B) {
    if (A.length !== B.length) return false;
    for (let i = 0; i < A.length; i++) {
        if (A[i].length !== B[i].length) return false;
        for (let j = 0; j < A[i].length; j++) if (A[i][j] !== B[i][j]) return false;
    }
    return true;
}
function copyMat(A) { return A.map(r => r.slice()); }

function invUnitri(U) {
    const n = U.length, X = zeros(n);
    for (let j = 0; j < n; j++) {
        for (let i = n - 1; i >= 0; i--) {
            let s = 0n;
            for (let k = i + 1; k < n; k++) s += U[i][k] * X[k][j];
            X[i][j] = (i === j ? 1n : 0n) - s;
        }
    }
    return X;
}

function fracDet(A) {
    const n = A.length, M = A.map(r => r.map(qi)); let d = Q1;
    for (let c = 0; c < n; c++) {
        let p = -1;
        for (let r = c; r < n; r++) if (!qzero(M[r][c])) { p = r; break; }
        if (p < 0) return Q0;
        if (p !== c) { const t = M[c]; M[c] = M[p]; M[p] = t; d = qneg(d); }
        d = qmul(d, M[c][c]);
        for (let r = c + 1; r < n; r++) {
            if (!qzero(M[r][c])) {
                const f = qdiv(M[r][c], M[c][c]), Mr = M[r], Mc = M[c];
                M[r] = Mr.map((x, i) => qsub(x, qmul(f, Mc[i])));
            }
        }
    }
    return d;
}

function intInverse(G) {
    const n = G.length;
    const A = G.map((r, i) => r.map(qi).concat(Array.from({ length: n }, (_, j) => i === j ? Q1 : Q0)));
    for (let c = 0; c < n; c++) {
        let p = -1;
        for (let r = c; r < n; r++) if (!qzero(A[r][c])) { p = r; break; }
        if (p < 0) return null;
        const t = A[c]; A[c] = A[p]; A[p] = t;
        const d = A[c][c]; A[c] = A[c].map(x => qdiv(x, d));
        for (let r = 0; r < n; r++) {
            if (r !== c && !qzero(A[r][c])) {
                const f = A[r][c], Ar = A[r], Ac = A[c];
                A[r] = Ar.map((x, i) => qsub(x, qmul(f, Ac[i])));
            }
        }
    }
    const X = A.map(r => r.slice(n));
    for (const r of X) for (const x of r) if (x.d !== 1n) return null;
    return X.map(r => r.map(x => x.n));
}

// =====================================================================================================================
// quivers
// =====================================================================================================================

function toBigMatrix(B) {
    return B.map(r => r.map(x => {
        if (typeof x === 'bigint') return x;
        if (typeof x === 'number') { if (!Number.isInteger(x)) throw new Error('B must have integer entries'); return BigInt(x); }
        if (typeof x === 'string' && /^\s*[-+]?\d+\s*$/.test(x)) return BigInt(x.trim());
        throw new Error('B must have integer entries');
    }));
}

function checkSkew(B) {
    const n = B.length;
    if (B.some(r => r.length !== n)) throw new Error('B must be square');
    for (let i = 0; i < n; i++)
        for (let j = 0; j < n; j++) {
            if (typeof B[i][j] !== 'bigint') throw new Error('B must have integer entries');
            if (B[i][j] !== -B[j][i]) throw new Error('B must be skew-symmetric');
        }
}

function fromUpper(q, n) {
    q = q.map(x => BigInt(x));
    if (n === undefined) n = Math.round((1 + Math.sqrt(1 + 8 * q.length)) / 2);
    if (n * (n - 1) / 2 !== q.length) throw new Error('upper tuple has wrong length');
    const B = zeros(n); let p = 0;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) { B[i][j] = q[p]; B[j][i] = -q[p]; p++; }
    return B;
}

function upper(B) {
    const n = B.length, out = [];
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) out.push(B[i][j]);
    return out;
}

function mutate(B, k) {
    const n = B.length, B2 = zeros(n);
    for (let i = 0; i < n; i++)
        for (let j = 0; j < n; j++) {
            if (i === k || j === k) B2[i][j] = -B[i][j];
            else {
                const a = B[i][k], b = B[k][j];
                B2[i][j] = B[i][j] + ((a > 0n && b > 0n) ? a * b : ((a < 0n && b < 0n) ? -a * b : 0n));
            }
        }
    return B2;
}

function isAcyclic(B) {
    const n = B.length, rem = new Set();
    for (let i = 0; i < n; i++) rem.add(i);
    while (rem.size) {
        let src = -1;
        const sorted = Array.from(rem).sort((a, b) => a - b);
        for (const v of sorted) {
            let ok = true;
            for (const w of rem) if (B[w][v] > 0n) { ok = false; break; }
            if (ok) { src = v; break; }
        }
        if (src < 0) return false;
        rem.delete(src);
    }
    return true;
}

function components(B) {
    const n = B.length, seen = new Set(), comps = [];
    for (let s0 = 0; s0 < n; s0++) {
        if (seen.has(s0)) continue;
        const comp = [s0], st = [s0]; seen.add(s0);
        while (st.length) {
            const i = st.pop();
            for (let j = 0; j < n; j++) if (B[i][j] !== 0n && !seen.has(j)) { seen.add(j); comp.push(j); st.push(j); }
        }
        comps.push(comp.sort((a, b) => a - b));
    }
    return comps;
}

function isConnected(B) { return components(B).length <= 1; }

// lexicographic permutations of [0..n-1], same order as itertools.permutations(range(n))
function* permutations(arr) {
    const a = arr.slice(), n = a.length;
    yield a.slice();
    if (n < 2) return;
    while (true) {
        let i = n - 2;
        while (i >= 0 && a[i] >= a[i + 1]) i--;
        if (i < 0) return;
        let j = n - 1;
        while (a[j] <= a[i]) j--;
        let t = a[i]; a[i] = a[j]; a[j] = t;
        for (let l = i + 1, r = n - 1; l < r; l++, r--) { t = a[l]; a[l] = a[r]; a[r] = t; }
        yield a.slice();
    }
}
function range(n) { return Array.from({ length: n }, (_, i) => i); }

function tupleCmp(a, b) {
    for (let i = 0; i < a.length && i < b.length; i++) { if (a[i] < b[i]) return -1; if (a[i] > b[i]) return 1; }
    return a.length - b.length;
}

function canonical(B) {
    const n = B.length; let best = null;
    for (const p of permutations(range(n))) {
        const t = [];
        for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) t.push(B[p[i]][p[j]]);
        if (best === null || tupleCmp(t, best) < 0) best = t;
    }
    return best;
}

/** canonical representative of the sink/source reflection class of an acyclic quiver (Caldero-Keller). */
function reflectionClass(B0) {
    const n = B0.length, c0 = canonical(B0), seen = new Map([[c0.join(','), c0]]), stack = [B0];
    while (stack.length) {
        const X = stack.pop();
        for (let v = 0; v < n; v++) {
            let sink = true, source = true;
            for (let w = 0; w < n; w++) { if (X[v][w] > 0n) sink = false; if (X[v][w] < 0n) source = false; }
            if (sink || source) {
                const Y = mutate(X, v), cY = canonical(Y), key = cY.join(',');
                if (!seen.has(key)) { seen.set(key, cY); stack.push(Y); }
            }
        }
    }
    let best = null;
    for (const t of seen.values()) if (best === null || tupleCmp(t, best) < 0) best = t;
    return best;
}

function companion(B, order) {
    const n = B.length, U = zeros(n);
    for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) U[a][b] = a === b ? 1n : (a < b ? -B[order[a]][order[b]] : 0n);
    return U;
}
function coxeter(U) { return negMat(matMul(invUnitri(U), transpose(U))); }
function coxeterInverse(U) { return negMat(matMul(transpose(invUnitri(U)), U)); }
function sym(U) { const n = U.length, S = zeros(n); for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) S[i][j] = U[i][j] + U[j][i]; return S; }

function mod(a, n) { return ((a % n) + n) % n; }
function properCyclicOrders(B) {
    const n = B.length, res = [];
    for (const rest of permutations(range(n).slice(1))) {
        const perm = [0].concat(rest), pos = {}; let ok = true;
        perm.forEach((v, i) => { pos[v] = i; });
        for (let v = 0; v < n && ok; v++) {
            const ins = range(n).filter(a => B[a][v] > 0n), outs = range(n).filter(b => B[v][b] > 0n);
            for (const a of ins) {
                for (const b of outs) if (!(mod(pos[v] - pos[a], n) < mod(pos[b] - pos[a], n))) { ok = false; break; }
                if (!ok) break;
            }
        }
        if (ok) res.push(perm);
    }
    return res;
}
function properRotations(B) {
    const n = B.length, out = [], seen = new Set();
    for (const p of properCyclicOrders(B))
        for (let r = 0; r < n; r++) {
            const o = p.slice(r).concat(p.slice(0, r)), key = o.join(',');
            if (!seen.has(key)) { seen.add(key); out.push(o); }
        }
    return out;
}

// =====================================================================================================================
// polynomials: BigInt coefficient arrays, lowest degree first
// =====================================================================================================================

function ptrim(p) { let e = p.length; while (e > 0 && p[e - 1] === 0n) e--; return e === p.length ? p : p.slice(0, e); }
function padd(a, b) {
    const n = Math.max(a.length, b.length), r = new Array(n);
    for (let i = 0; i < n; i++) r[i] = (i < a.length ? a[i] : 0n) + (i < b.length ? b[i] : 0n);
    return ptrim(r);
}
function psub(a, b) {
    const n = Math.max(a.length, b.length), r = new Array(n);
    for (let i = 0; i < n; i++) r[i] = (i < a.length ? a[i] : 0n) - (i < b.length ? b[i] : 0n);
    return ptrim(r);
}
function pscale(a, k) { return k !== 0n ? ptrim(a.map(x => k * x)) : []; }
function pmul(a, b) {
    if (!a.length || !b.length) return [];
    const r = new Array(a.length + b.length - 1).fill(0n);
    for (let i = 0; i < a.length; i++) {
        const x = a[i];
        if (x !== 0n) for (let j = 0; j < b.length; j++) r[i + j] += x * b[j];
    }
    return ptrim(r);
}
function pderiv(a) { const r = []; for (let i = 1; i < a.length; i++) r.push(BigInt(i) * a[i]); return ptrim(r); }

/** quotient and remainder of the integer polynomial a by the monic integer polynomial h. */
function pdivmodMonic(a, h) {
    a = a.slice(); const d = h.length - 1, q = new Array(Math.max(0, a.length - d)).fill(0n);
    for (let i = a.length - 1; i >= d; i--) {
        const c = a[i];
        if (c !== 0n) {
            q[i - d] = c;
            for (let j = 0; j <= d; j++) a[i - d + j] -= c * h[j];
        }
    }
    return [ptrim(q), ptrim(a.slice(0, d))];
}
function pmodMonic(a, h) {
    if (a.length < h.length) return ptrim(a.slice(0, h.length - 1));
    return pdivmodMonic(a, h)[1];
}
/** sum_k coeffs[k] * polys[k]. */
function lin(coeffs, polys) {
    let r = [];
    const m = Math.min(coeffs.length, polys.length);
    for (let k = 0; k < m; k++) if (coeffs[k] !== 0n) r = padd(r, pscale(polys[k], coeffs[k]));
    return r;
}

// rational polynomials (arrays of Q), only for gcds and Sturm sequences
function qtrim(p) { let e = p.length; while (e > 0 && qzero(p[e - 1])) e--; return p.slice(0, e); }
function qdivmod(a, b) {
    a = a.map(qi); b = qtrim(b.map(qi));
    const q = new Array(Math.max(0, a.length - b.length + 1)).fill(Q0);
    while (qtrim(a).length >= b.length) {
        a = qtrim(a);
        const c = qdiv(a[a.length - 1], b[b.length - 1]), s = a.length - b.length;
        q[s] = c;
        for (let j = 0; j < b.length; j++) a[s + j] = qsub(a[s + j], qmul(c, b[j]));
        a = qtrim(a);
        if (!a.length) break;
    }
    return [qtrim(q), qtrim(a)];
}
function qgcd(a, b) {
    a = qtrim(a.map(qi)); b = qtrim(b.map(qi));
    while (b.length) { const r = qdivmod(a, b)[1]; a = b; b = r; }
    if (!a.length) return [];
    const lc = a[a.length - 1];
    return a.map(x => qdiv(x, lc));
}
function qeval(p, x) { let r = Q0; for (let i = p.length - 1; i >= 0; i--) r = qadd(qmul(r, x), qi(p[i])); return r; }
/** positive multiple of a rational polynomial with coprime integer coefficients. */
function toIntPoly(p) {
    p = p.map(qi); let den = 1n;
    for (const c of p) den = den * c.d / bgcd(den, c.d);
    const q = p.map(c => c.n * (den / c.d)); let g = 0n;
    for (const c of q) g = bgcd(g, c);
    return g !== 0n ? q.map(c => c / g) : q;
}

// =====================================================================================================================
// characteristic polynomial, adjugate, cyclotomic factors, root isolation
// =====================================================================================================================

/** Faddeev-LeVerrier: charpoly f of c (lowest degree first, monic) and integer matrices B_0..B_{n-1} with
 *  adj(x I - c) = sum_k x^(n-1-k) B_k. */
function flAdjugate(c) {
    const n = c.length, Bs = [identity(n)], a = [1n];
    for (let k = 1; k <= n; k++) {
        const AB = matMul(c, Bs[Bs.length - 1]); let tr = 0n;
        for (let i = 0; i < n; i++) tr += AB[i][i];
        if (tr % BigInt(k) !== 0n) throw new Error('Faddeev-LeVerrier: trace not divisible');
        const ak = -tr / BigInt(k); a.push(ak);
        if (k < n) Bs.push(AB.map((r, i) => r.map((x, j) => x + (i === j ? ak : 0n))));
    }
    return [a.slice().reverse(), Bs];
}

const CYC = new Map();
function cyclotomic(d) {
    if (!CYC.has(d)) {
        let p = new Array(d + 1).fill(0n); p[0] = -1n; p[d] = 1n;
        for (let e = 1; e < d; e++) {
            if (d % e === 0) {
                const qr = pdivmodMonic(p, cyclotomic(e));
                if (qr[1].length) throw new Error('cyclotomic division');
                p = qr[0];
            }
        }
        CYC.set(d, p);
    }
    return CYC.get(d);
}

/** remove all cyclotomic factors; phi(d) >= sqrt(d/2), so d <= 2 n^2 suffices. */
function stripCyclotomic(f) {
    let g = f.slice(); const n = f.length - 1;
    for (let d = 1; d < 2 * n * n + 3; d++) {
        const c = cyclotomic(d);
        if (c.length - 1 > n) continue;
        while (g.length >= c.length) {
            const qr = pdivmodMonic(g, c);
            if (qr[1].length) break;
            g = qr[0];
        }
    }
    return g;
}

/** g / gcd(g, g') for a monic integer polynomial g; the result is monic with integer coefficients. */
function squarefreePart(g) {
    const d = qgcd(g, pderiv(g));
    if (d.length <= 1) return g.slice();
    const qr = qdivmod(g, d);
    if (qr[1].length) throw new Error('squarefree_part: nonzero remainder');
    return qr[0].map(x => { if (x.d !== 1n) throw new Error('squarefree_part: non-integral'); return x.n; });
}

function sturmSequence(h) {
    const seq = [h.map(qi), pderiv(h).map(qi)];
    while (seq[seq.length - 1].length > 1) {
        const r = qdivmod(seq[seq.length - 2], seq[seq.length - 1])[1];
        if (!r.length) break;
        seq.push(r.map(qneg));
    }
    return seq;
}
function signChanges(seq, x) {
    const vals = [];
    for (const p of seq) { const v = qeval(p, x); if (!qzero(v)) vals.push(v); }
    let s = 0;
    for (let i = 0; i + 1 < vals.length; i++) if ((qsign(vals[i]) > 0) !== (qsign(vals[i + 1]) > 0)) s++;
    return s;
}
/** isolating interval (lo, hi) with dyadic endpoints for the largest real root of h, if that root is > 1. */
function largestRootAboveOne(h) {
    const seq = sturmSequence(h);
    let mx = 0n;
    for (let i = 0; i < h.length - 1; i++) if (babs(h[i]) > mx) mx = babs(h[i]);
    const B = qi(1n + mx);
    const count = (a, b) => signChanges(seq, a) - signChanges(seq, b);
    if (count(Q1, B) === 0) return null;
    let lo = Q1, hi = B;
    while (count(lo, hi) > 1) {
        const mid = qdiv(qadd(lo, hi), qi(2n));
        if (count(mid, hi) >= 1) lo = mid; else hi = mid;
    }
    return [lo, hi];
}

/** the real algebraic number rho > 1: a monic squarefree integer polynomial h and an isolating interval
 *  [L/2^k, H/2^k] with h(L/2^k) h(H/2^k) < 0. Elements of Q(rho) are integer polynomials in rho. */
class Rho {
    constructor(h, lo, hi) {
        this.h = h.slice(); this.d = h.length - 1;
        let k = 0n;
        while (((1n << k) % lo.d) !== 0n || ((1n << k) % hi.d) !== 0n) k += 1n;
        this.k = k; this.L = lo.n * ((1n << k) / lo.d); this.H = hi.n * ((1n << k) / hi.d);
        this._pw = null;
        this.sL = this._sgnAt(this.h, this.L);
        if (this.sL === 0 || this._sgnAt(this.h, this.H) !== -this.sL) throw new Error('Rho: not an isolating interval');
    }
    _numAt(p, X) {                                    // numerator of p(X/2^k), over the denominator 2^(k deg p)
        const e = p.length - 1, k = this.k; let s = 0n, Xi = 1n;
        for (let i = 0; i < p.length; i++) {
            if (p[i] !== 0n) s += (p[i] * Xi) << (k * BigInt(e - i));
            Xi *= X;
        }
        return s;
    }
    _sgnAt(p, X) { return bsgn(this._numAt(p, X)); }
    refine() {
        const M = this.L + this.H; this.k += 1n; this.L *= 2n; this.H *= 2n; this._pw = null;
        const s = this._sgnAt(this.h, M);
        if (s === 0) throw new Error('Rho.refine hit a root');
        if (s === this.sL) this.L = M; else this.H = M;
    }
    refineTo(bits) { const b = BigInt(bits); while (((this.H - this.L) << b) > (1n << this.k)) this.refine(); }
    lo() { return qn(this.L, 1n << this.k); }
    hi() { return qn(this.H, 1n << this.k); }
    _powers(e) {                                      // [L^i << k(e-i)], [H^i << k(e-i)] for the current interval
        let pw = this._pw;
        if (pw === null) pw = this._pw = { L: [1n], H: [1n], sh: new Map() };
        while (pw.L.length <= e) { pw.L.push(pw.L[pw.L.length - 1] * this.L); pw.H.push(pw.H[pw.H.length - 1] * this.H); }
        let s = pw.sh.get(e);
        if (!s) {
            const k = this.k, Ls = [], Hs = [];
            for (let i = 0; i <= e; i++) { const sh = k * BigInt(e - i); Ls.push(pw.L[i] << sh); Hs.push(pw.H[i] << sh); }
            s = [Ls, Hs]; pw.sh.set(e, s);
        }
        return s;
    }
    /** [lo, hi, den]: p(rho) lies in [lo/den, hi/den] (p(rho) is monotone in each coefficient sign class, rho > 0). */
    boundsRaw(p) {
        if (!p.length) return [0n, 0n, 1n];
        const e = p.length - 1, s = this._powers(e), Ls = s[0], Hs = s[1]; let lo = 0n, hi = 0n;
        for (let i = 0; i <= e; i++) {
            const c = p[i];
            if (c > 0n) { lo += c * Ls[i]; hi += c * Hs[i]; }
            else if (c < 0n) { lo += c * Hs[i]; hi += c * Ls[i]; }
        }
        return [lo, hi, 1n << (this.k * BigInt(e))];
    }
    bounds(p) { const b = this.boundsRaw(p); return [qn(b[0], b[2]), qn(b[1], b[2])]; }
    reduce(p) { return pmodMonic(p, this.h); }
    isZero(p) {
        p = this.reduce(p);
        if (!p.length) return true;
        const g = qgcd(p, this.h);
        if (g.length <= 1) return false;
        const gi = toIntPoly(g);
        return this._sgnAt(gi, this.L) * this._sgnAt(gi, this.H) < 0;
    }
    sign(p) {
        p = this.reduce(p);
        if (!p.length) return 0;
        for (let t = 0; t < Rho.TRY; t++) {
            const b = this.boundsRaw(p);
            if (b[0] > 0n) return 1;
            if (b[1] < 0n) return -1;
            this.refine();
        }
        if (this.isZero(p)) return 0;
        while (true) {
            const b = this.boundsRaw(p);
            if (b[0] > 0n) return 1;
            if (b[1] < 0n) return -1;
            this.refine();
        }
    }
    /** a positive lower bound for |p(rho)| (p(rho) must be nonzero), tight within a factor 9/8. */
    absLo(p) {
        p = this.reduce(p);
        if (this.sign(p) === 0) throw new Error('absLo of zero');
        while (true) {
            const b = this.boundsRaw(p), lo = b[0], hi = b[1];
            if (lo > 0n && 8n * (hi - lo) <= lo) return qn(lo, b[2]);
            if (hi < 0n && 8n * (hi - lo) <= -hi) return qn(-hi, b[2]);
            this.refine();
        }
    }
    absHi(p) { const b = this.boundsRaw(this.reduce(p)); return qn(bmax(babs(b[0]), babs(b[1])), b[2]); }
}
Rho.TRY = 48;

/** exact Schur-Cohn test: all roots of f(rho x)/(x - 1) lie in the open unit disk, i.e. rho is a simple root of
 *  f and every other root has modulus < rho. */
function strictlyDominant(f, R) {
    const n = f.length - 1, F = [];
    for (let i = 0; i <= n; i++) { if (f[i] !== 0n) { const p = new Array(i + 1).fill(0n); p[i] = f[i]; F.push(p); } else F.push([]); }
    const Qs = new Array(n); Qs[n - 1] = F[n];
    for (let i = n - 1; i > 0; i--) Qs[i - 1] = padd(F[i], Qs[i]);
    if (R.sign(padd(F[0], Qs[0])) !== 0) return false;
    let a = Qs.map(q => R.reduce(q));
    while (a.length > 1) {
        const d = a.length - 1, a0 = a[0], ad = a[d];
        if (R.sign(pmul(psub(ad, a0), padd(ad, a0))) <= 0) return false;
        const b = [];
        for (let i = 0; i < d; i++) b.push(R.reduce(psub(pmul(ad, a[i + 1]), pmul(a0, a[d - 1 - i]))));
        a = b;
    }
    return true;
}

// =====================================================================================================================
// outward-rounded dyadic interval matrices (for the certificate window)
// Entries are pairs [lo, hi] of BigInt numerators over the fixed denominator 2^P. This is the same arithmetic as the
// Python reference (Fractions rounded to multiples of 2^-P after every product and every sum), stored scaled.
// =====================================================================================================================

function rdScaled(x, P) { return qfloor(new Q(x.n << BigInt(P), x.d)); }          // floor(x 2^P)
function ruScaled(x, P) { return qceil(new Q(x.n << BigInt(P), x.d)); }           // ceil(x 2^P)

function ivmatMulScaled(X, Y, P) {
    const Pb = BigInt(P), n = X.length, m = Y[0].length, l = Y.length, out = [];
    for (let i = 0; i < n; i++) {
        const row = [];
        for (let j = 0; j < m; j++) {
            let lo = 0n, hi = 0n;
            for (let k = 0; k < l; k++) {
                const a = X[i][k], b = Y[k][j];
                const p0 = a[0] * b[0], p1 = a[0] * b[1], p2 = a[1] * b[0], p3 = a[1] * b[1];
                let mn = p0, mx = p0;
                if (p1 < mn) mn = p1; if (p1 > mx) mx = p1;
                if (p2 < mn) mn = p2; if (p2 > mx) mx = p2;
                if (p3 < mn) mn = p3; if (p3 > mx) mx = p3;
                lo += mn >> Pb;                       // floor(mn / 2^P)
                hi += -((-mx) >> Pb);                 // ceil(mx / 2^P)
            }
            row.push([lo, hi]);
        }
        out.push(row);
    }
    return out;
}
function ivmatNormScaled(X) {                         // numerator over 2^P of max_row sum max(|lo|, |hi|)
    if (!X.length) return 0n;
    let best = null;
    for (const row of X) {
        let s = 0n;
        for (const e of row) s += bmax(babs(e[0]), babs(e[1]));
        if (best === null || s > best) best = s;
    }
    return best;
}
function ivDiv(a, b) {
    if (!(qsign(b[0]) > 0 || qsign(b[1]) < 0)) throw new Error('iv_div by an interval containing 0');
    const q0 = qdiv(a[0], b[0]), q1 = qdiv(a[0], b[1]), q2 = qdiv(a[1], b[0]), q3 = qdiv(a[1], b[1]);
    return [qmin4(q0, q1, q2, q3), qmax4(q0, q1, q2, q3)];
}
/** smallest integer r >= 0 with r^p >= x. */
function irootCeil(x, p) {
    if (x <= 1n) return x > 0n ? x : 0n;
    const pb = BigInt(p);
    let r = 1n << BigInt(Math.floor((bitLength(x) + p - 1) / p));
    while (true) {
        const s = ((pb - 1n) * r + x / (r ** (pb - 1n))) / pb;
        if (s >= r) break;
        r = s;
    }
    while (r ** pb > x) r -= 1n;
    while (r ** pb < x) r += 1n;
    return r;
}

/** the number of passes of `while val <= U: val *= ratio` starting from val = L, i.e. the least m >= 0 with
 *  L ratio^m > U, for L, U > 0 and ratio > 1. Exact: exponential then binary search on integer cross-products,
 *  which gives the same m as the loop without its m gcd-normalized multiplications. */
function stepsAbove(L, U, ratio) {
    if (!(L.n > 0n && U.n > 0n && ratio.n > ratio.d)) {        // outside the guaranteed regime: run the loop itself
        let m = 0, val = L;
        while (qcmp(val, U) <= 0) { val = qmul(val, ratio); m++; }
        return m;
    }
    const A = U.n * L.d, Bv = L.n * U.d, rn = ratio.n, rd = ratio.d;
    const above = m => Bv * rn ** BigInt(m) > A * rd ** BigInt(m);
    if (above(0)) return 0;
    let lo = 0, hi = 1;                                         // invariant: !above(lo)
    while (!above(hi)) { lo = hi; hi *= 2; }
    while (hi - lo > 1) { const mid = lo + Math.floor((hi - lo) / 2); if (above(mid)) hi = mid; else lo = mid; }
    return hi;
}

// =====================================================================================================================
// one linear order
// =====================================================================================================================

// Spectral data and grids are cached by the characteristic polynomial f, as in the Python reference: orders with the
// same Coxeter polynomial share one Rho, including its refinements, so the refinement state (and with it the grid
// values s and the certificate windows) evolves exactly as in the reference. The caches are cleared at the start of
// every top-level decide(); nested decides (4-vertex subquivers) share them.
const SPEC_CACHE = new Map(), GRID_CACHE = new Map();

/** 'unit', 'none', or the Rho of a strictly dominant real root rho > 1 of f; cached by (f, dominance). With
 *  dominance = false the largest real root rho > 1 is returned if it is a simple root of f, without the Schur-Cohn
 *  test, whose bit sizes grow exponentially with n (audit2 fix 6). SELECT uses this: at a mutation-acyclic input rho is strictly dominant anyway
 *  (H5), and orders built this way are never given to gelfand() or window(), which need the gap. */
function spectral(f, dominance) {
    const key = f.join(',') + (dominance ? '|d' : '|n');
    if (!SPEC_CACHE.has(key)) {
        const g = stripCyclotomic(f); let res;
        if (g.length <= 1) res = 'unit';
        else {
            const h = squarefreePart(g), iv = largestRootAboveOne(h);
            if (iv === null) res = 'none';
            else {
                const R = new Rho(h, iv[0], iv[1]);
                if (dominance) res = strictlyDominant(f, R) ? R : 'none';
                else res = R.sign(R.reduce(pderiv(f))) !== 0 ? R : 'none';     // rho simple (H5)
            }
        }
        if (SPEC_CACHE.size > 10000) { SPEC_CACHE.clear(); GRID_CACHE.clear(); }
        SPEC_CACHE.set(key, res);
    }
    return SPEC_CACHE.get(key);
}

/** data for one linear order sigma: companion U, Coxeter matrix c, and, if c has a strictly dominant real
 *  eigenvalue rho > 1 (type 'wild'), the eigen-functionals lam_+, lam_- and eigenvectors y_+, y_- as integer
 *  polynomials in rho. Other types: 'unit' (cyclotomic characteristic polynomial) and 'none'.
 *  dominance = false skips the strict-dominance test (SELECT; see spectral()). */
class ExactOrder {
    constructor(B, order, dominance) {
        if (dominance === undefined) dominance = true;
        this.order = order.slice(); const n = B.length; this.n = n;
        this.U = companion(B, order); this.c = coxeter(this.U); this.ci = coxeterInverse(this.U);
        const fl = flAdjugate(this.c), f = fl[0], Bs = fl[1]; this.f = f;
        this._pow = new Map([[0, identity(n)]]); this._gel = new Map();
        const spec = spectral(f, dominance);          // depends only on f (shared by orders with congruent companions)
        if (spec === 'unit' || spec === 'none') { this.type = spec; return; }
        const R = spec; this.R = R;
        // adj(rho I - c)_{ij} = sum_d (B_{n-1-d})_{ij} rho^d ;  rho^{n-1} adj(rho^{-1} I - c)_{ij} = sum_d (B_d)_{ij} rho^d
        const Pp = [], Pm = [];
        for (let i = 0; i < n; i++) {
            const rp = [], rm = [];
            for (let j = 0; j < n; j++) {
                const cp = [], cm = [];
                for (let d = 0; d < n; d++) { cp.push(Bs[n - 1 - d][i][j]); cm.push(Bs[d][i][j]); }
                rp.push(R.reduce(ptrim(cp))); rm.push(R.reduce(ptrim(cm)));
            }
            Pp.push(rp); Pm.push(rm);
        }
        const nonzeroRow = P => {
            for (let i = 0; i < n; i++) for (const e of P[i]) if (R.sign(e) !== 0) return P[i];
            throw new Error('StopIteration: no nonzero row');
        };
        const nonzeroCol = P => {
            for (let j = 0; j < n; j++) for (let i = 0; i < n; i++) if (R.sign(P[i][j]) !== 0) return P.map(r => r[j]);
            throw new Error('StopIteration: no nonzero column');
        };
        this.lp = nonzeroRow(Pp); this.yp = nonzeroCol(Pp);
        this.lm = nonzeroRow(Pm); this.ym = nonzeroCol(Pm);
        // relative sign: chi_U(x, x) > 0 for lam_+ + lam_- = chi_U(x, -)
        const Ui = invUnitri(this.U), ph = this.lp.map((a, i) => padd(a, this.lm[i])); let q = [];
        for (let j = 0; j < n; j++)
            for (let k = 0; k < n; k++)
                if (Ui[j][k] !== 0n) q = padd(q, pscale(pmul(ph[j], ph[k]), Ui[j][k]));
        const sq = R.sign(q);
        if (sq === 0) { this.type = 'none'; return; }
        if (sq < 0) this.lm = this.lm.map(p => pscale(p, -1n));
        this.type = 'wild';
    }

    /** c^m as an exact integer matrix (m may be negative); computed iteratively and cached. */
    power(m) {
        if (!this._pow.has(m)) {
            const step = m > 0 ? 1 : -1, M = m > 0 ? this.c : this.ci;
            let j = m;
            while (!this._pow.has(j - step)) j -= step;
            for (let i = j; i !== m + step; i += step) this._pow.set(i, matMul(M, this._pow.get(i - step)));
        }
        return this._pow.get(m);
    }

    /** 2n+1 rational values s_j with s_j^(8(2n+1)) in [rho^(8j-1), rho^(8j+1)], j = 0..2n (cached by f). */
    grid() {
        const key = this.f.join(',') + '|' + this.n;
        if (!GRID_CACHE.has(key)) GRID_CACHE.set(key, this._grid());
        return GRID_CACHE.get(key).slice();
    }

    _grid() {
        const n = this.n, K = 8 * (2 * n + 1), R = this.R, out = [Q1];
        for (let j = 1; j <= 2 * n; j++) {
            let Tlo, Thi;
            while (true) {
                Tlo = qpow(R.hi(), 8 * j - 1); Thi = qpow(R.lo(), 8 * j + 1);
                if (qlt(Tlo, Thi)) break;
                R.refine();
            }
            let a = Q1, b = R.hi();
            while (true) {
                const m = qdiv(qadd(a, b), qi(2n)), v = qpow(m, K);
                if (qlt(v, Tlo)) a = m;
                else if (qlt(Thi, v)) b = m;
                else { out.push(m); break; }
            }
        }
        return out;
    }

    /** constants (theta, C, t, Kb) with theta < rho such that ||M^m v||_inf <= Kb C theta^m ||v without coord t||_inf
     *  for all m >= 0 and all v with lam(v) = 0, where (M, lam) = (c, lam_+) or (c^{-1}, lam_-). */
    gelfand(direction) {
        if (this._gel.has(direction)) return this._gel.get(direction);
        const R = this.R, n = this.n;
        const M = direction > 0 ? this.c : this.ci, lam = direction > 0 ? this.lp : this.lm;
        const nz = [];
        for (let i = 0; i < n; i++) if (R.sign(lam[i]) !== 0) nz.push(i);
        let t = -1, tkey = null;                      // Python max(nz, key=...): keys in order, first maximum
        for (const i of nz) { const kv = R.absLo(lam[i]); if (t < 0 || qcmp(kv, tkey) > 0) { t = i; tkey = kv; } }
        const idx = range(n).filter(i => i !== t);
        let P = 64;
        while (true) {
            R.refineTo(P + 16); const lt = R.bounds(lam[t]);
            const ratio = {};
            for (const i of idx) ratio[i] = ivDiv(R.bounds(lam[i]), lt);
            const A = idx.map(j => idx.map(i => {
                const Mji = qi(M[j][i]), Mjt = qi(M[j][t]);
                const x0 = qmul(ratio[i][0], Mjt), x1 = qmul(ratio[i][1], Mjt);
                return [rdScaled(qsub(Mji, qmaxv(x0, x1)), P), ruScaled(qsub(Mji, qminv(x0, x1)), P)];
            }));
            let Kb = Q1;
            for (const i of idx) Kb = qadd(Kb, qmaxv(qabs(ratio[i][0]), qabs(ratio[i][1])));
            const rlo = R.lo(); let S = A, pw = 1;
            const one = 1n << BigInt(P), floorTheta = new Q(1n, one);
            for (let q = 1; q < 6 + Math.floor(P / 32); q++) {
                S = ivmatMulScaled(S, S, P); pw *= 2;
                const Nnum = ivmatNormScaled(S);       // N = Nnum / 2^P, so ceil(N 2^(P pw)) = Nnum 2^(P (pw - 1))
                const theta = qmaxv(qn(irootCeil(Nnum << BigInt(P * (pw - 1)), pw), one), floorTheta);
                if (qlt(theta, rlo)) {
                    let C = Q1, Ab = idx.map((_, i) => idx.map((_, j) => i === j ? [one, one] : [0n, 0n]));
                    for (let e = 1; e < pw; e++) {
                        Ab = ivmatMulScaled(Ab, A, P);
                        C = qmaxv(C, qdiv(qn(ivmatNormScaled(Ab), one), qpow(theta, e)));
                    }
                    const res = [theta, C, t, Kb];
                    this._gel.set(direction, res);
                    return res;
                }
            }
            P *= 2;
        }
    }

    /** (m_plus, m_minus) such that the sign patterns of C_m are constant for m >= m_plus and for m <= -m_minus;
     *  null if some needed quantity vanishes (this never happens at a seed order). */
    window(G) {
        const R = this.R, n = this.n;
        const Gi = intInverse(G);
        if (Gi === null) return null;
        const GiT = transpose(Gi);
        let normGiT = null;
        for (const r of GiT) { let s = 0n; for (const x of r) s += babs(x); if (normGiT === null || s > normGiT) normGiT = s; }
        const out = [];
        for (const direction of [1, -1]) {
            const lam = direction > 0 ? this.lp : this.lm, y = direction > 0 ? this.yp : this.ym;
            const w = range(n).map(i => lin(GiT[i], y));
            for (const wi of w) if (R.sign(wi) === 0) return null;
            for (let k = 0; k < n; k++) if (R.sign(lam[k]) === 0) return null;
            const gel = this.gelfand(direction), theta = gel[0], C = gel[1], t = gel[2], Kb = gel[3];
            let den = [];
            for (let k = 0; k < n; k++) den = padd(den, pmul(lam[k], y[k]));
            const denLo = R.absLo(den), denHi = R.absHi(den);
            let wmin = null;
            for (const wi of w) { const v = R.absLo(wi); if (wmin === null || qcmp(v, wmin) < 0) wmin = v; }
            const ratio = qdiv(R.lo(), theta); let mdir = 0;
            for (let k = 0; k < n; k++) {
                // alo, ahi, Lk, rk, Uk only enter comparisons, so they are kept unnormalized (same values, no gcds)
                const alo = rdiv(R.absLo(lam[k]), denHi), ahi = rdiv(R.absHi(lam[k]), denLo);
                const Lk = rmul(alo, wmin);
                let rk = null;
                for (let i = 0; i < n; i++) {
                    if (i === t) continue;
                    const v = radd(qi(i === k ? 1n : 0n), rmul(ahi, R.absHi(y[i])));
                    if (rk === null || qcmp(v, rk) > 0) rk = v;
                }
                const Uk = rmul(rmul(rmul(qi(normGiT), Kb), C), rk);
                // Python: m = 0; val = Lk; while val <= Uk: val *= ratio; m += 1
                mdir = Math.max(mdir, stepsAbove(Lk, Uk, ratio));
            }
            out.push(mdir);
        }
        return out;
    }
}

// =====================================================================================================================
// descent, walk, certificate
// =====================================================================================================================

/** Speyer-Thomas conditions in companion form: same sign a<b: U_ab <= 0; negative before positive: U_ab = 0. */
function stOk(U, eps) {
    const n = U.length;
    if (eps.some(e => e === 0)) return false;
    for (let a = 0; a < n; a++)
        for (let b = a + 1; b < n; b++) {
            if (eps[a] === eps[b] && U[a][b] > 0n) return false;
            if (eps[a] === -1 && eps[b] === 1 && U[a][b] !== 0n) return false;
        }
    return true;
}

/** exact greedy height descent towards s lam_+ + lam_-/s. -> [kind, Gamma rows], kind in obtuse, stuck, zero, cap. */
function descent(od, s, caps) {
    const g = descentGen(od, s, caps, 0);
    while (true) { const r = g.next(); if (r.done) return r.value; }
}

/** generator form of descent(): yields after every `chunk` steps (never if chunk is 0) and returns [kind, G]. */
function* descentGen(od, s, caps, chunk) {
    const R = od.R, n = od.n, S = sym(od.U), a = s.n, b = s.d;
    const Phi = range(n).map(k => R.reduce(padd(pscale(od.lp[k], a * a), pscale(od.lm[k], b * b))));
    const G = identity(n), Hs = Phi.slice(), sg = new Array(n).fill(1n);
    for (let i = 0; i < n; i++) {
        const si = R.sign(Hs[i]);
        if (si === 0) return ['zero', G];
        if (si < 0) { G[i] = G[i].map(x => -x); Hs[i] = pscale(Hs[i], -1n); sg[i] = -1n; }
    }
    const Gs = range(n).map(i => range(n).map(j => sg[i] * sg[j] * S[i][j]));
    let steps = 0;
    while (caps.stepsBelow(steps)) {
        const cands = [];
        for (let i = 0; i < n; i++)
            for (let j = 0; j < n; j++) {
                const al = Gs[i][j];
                if (i !== j && al > 0n && R.sign(psub(pscale(Hs[i], 2n), pscale(Hs[j], al))) > 0) {
                    const x = pscale(Hs[j], al), y = psub(pscale(Hs[i], 2n), x);
                    cands.push([i, j, al, R.sign(psub(y, x)) >= 0 ? x : y]);
                }
            }
        if (!cands.length) {
            let acute = false;
            for (let i = 0; i < n && !acute; i++) for (let j = i + 1; j < n; j++) if (Gs[i][j] > 0n) { acute = true; break; }
            return [acute ? 'stuck' : 'obtuse', G];
        }
        let best = cands[0];
        for (let c = 1; c < cands.length; c++) if (R.sign(psub(cands[c][3], best[3])) > 0) best = cands[c];
        const i = best[0], j = best[1], al = best[2];
        let v = range(n).map(k => G[i][k] - al * G[j][k]), hv = psub(Hs[i], pscale(Hs[j], al)), e = 1n;
        const sv = R.sign(hv);
        if (sv === 0) return ['zero', G];
        if (sv < 0) { v = v.map(x => -x); hv = pscale(hv, -1n); e = -1n; }
        G[i] = v; Hs[i] = hv;
        for (let k = 0; k < n; k++) if (k !== i) { Gs[i][k] = e * (Gs[i][k] - al * Gs[j][k]); Gs[k][i] = Gs[i][k]; }
        steps += 1;
        let mv = 0n;
        for (const x of v) if (babs(x) > mv) mv = babs(x);
        if (caps.above(mv)) return ['cap', G];
        if (chunk && steps % chunk === 0) yield steps;
    }
    return ['cap', G];
}

function gram(U, G) { return matMul(matMul(G, U), transpose(G)); }

function triOrder(Gm) {
    const n = Gm.length, rem = new Set(range(n)), order = [];
    for (let i = 0; i < n; i++) if (Gm[i][i] !== 1n) return null;
    while (rem.size) {
        let v = -1;
        for (const c of rem) {
            let ok = true;
            for (const x of rem) if (x !== c && Gm[x][c] !== 0n) { ok = false; break; }
            if (ok && (v < 0 || c < v)) v = c;
        }
        if (v < 0) return null;
        order.push(v); rem.delete(v);
    }
    return order;
}

function acyclicFromGamma(U, G) {
    const n = U.length, Gm = gram(U, G), pi = triOrder(Gm);
    if (pi === null) return null;
    const B0 = zeros(n);
    for (let x = 0; x < n; x++)
        for (let y = x + 1; y < n; y++) {
            const w = -Gm[pi[x]][pi[y]];
            if (w < 0n) return null;
            B0[x][y] = w; B0[y][x] = -w;
        }
    return [B0, pi];
}

function reflectBasis(U, G, i) {
    const n = U.length, S = sym(U), gi = G[i];
    const Sgi = range(n).map(b => { let s = 0n; for (let a = 0; a < n; a++) s += gi[a] * S[a][b]; return s; });
    return G.map((gj, j) => {
        if (j === i) return gi.map(x => -x);
        let p = 0n;
        for (let b = 0; b < n; b++) p += Sgi[b] * gj[b];
        return gj.map((x, k) => x - p * gi[k]);
    });
}

/** search m in [-m_minus, m_plus] with C_m = (Gamma-coordinates of c^m e_k)_k sign-coherent and satisfying st_ok
 *  (up to a global sign). -> [m, C, eps] or null. */
function certify(od, G, win) {
    const Gi = intInverse(G);
    if (Gi === null) return null;
    const mp = win[0], mm = win[1], ms = [0];
    for (let m = 1; m <= Math.max(mp, mm); m++) { if (m <= mp) ms.push(m); if (m <= mm) ms.push(-m); }
    for (const m of ms) {
        const C = matMul(transpose(od.power(m)), Gi); let eps = [];
        for (const r of C) {
            const any = r.some(x => x !== 0n);
            if (any && r.every(x => x >= 0n)) eps.push(1);
            else if (any && r.every(x => x <= 0n)) eps.push(-1);
            else { eps = null; break; }
        }
        if (eps === null) continue;
        if (stOk(od.U, eps)) return [m, C, eps];
        const neg = eps.map(x => -x);
        if (stOk(od.U, neg)) return [m, negMat(C), neg];
    }
    return null;
}

function packageCert(od, G, B0, pi, ce, s) {
    const m = ce[0], C = ce[1], eps = ce[2], n = od.n;
    const V = range(n).map(k => range(n).map(x => C[k][pi[x]]));
    return { kind: 'c-vectors', order: od.order.slice(), acyclic: B0, c_vectors: V, m: m, signs: eps, gamma: G,
             pi: pi.slice(), s: s.toString() };
}

/** axis walk through one period, starting from the chamber of the descent; certificate test in every chamber. */
function walk(od, G, s) {
    const R = od.R, n = od.n, a = s.n, b = s.d;
    for (let it = 0; it < n + 1; it++) {
        const aq = acyclicFromGamma(od.U, G);
        if (aq === null) return null;
        const B0 = aq[0], pi = aq[1];
        if (!isConnected(B0)) return null;
        const win = od.window(G);
        if (win === null) return null;
        const ce = certify(od, G, win);
        if (ce) return packageCert(od, G, B0, pi, ce, s);
        const A = G.map(g => lin(g, od.lp)), Bv = G.map(g => lin(g, od.lm)); let best = null;
        for (let i = 0; i < n; i++) {
            if (R.sign(A[i]) < 0) {
                // theta_i < theta_best  <=>  B_best A_i - B_i A_best < 0
                if (best === null || R.sign(psub(pmul(Bv[best], A[i]), pmul(Bv[i], A[best]))) < 0) best = i;
            }
        }
        if (best === null) return null;
        // end of the period: theta_best >= rho^2 s^2  <=>  b^2 B_best + a^2 rho^2 A_best >= 0
        if (R.sign(padd(pscale(Bv[best], b * b), pscale([0n, 0n].concat(A[best]), a * a))) >= 0) return null;
        G = reflectBasis(od.U, G, best);
    }
    return null;
}

/** mutation at k of the extended exchange matrix [B; C] (principal coefficients; C has the c-vectors as columns). */
function extendedMutate(B, C, k) {
    const n = B.length, C2 = zeros(n);
    for (let i = 0; i < n; i++)
        for (let j = 0; j < n; j++) {
            if (j === k) C2[i][j] = -C[i][j];
            else {
                const a = C[i][k], b = B[k][j];
                C2[i][j] = C[i][j] + ((a > 0n && b > 0n) ? a * b : ((a < 0n && b < 0n) ? -a * b : 0n));
            }
        }
    return [mutate(B, k), C2];
}

// binary min-heap on entries {f, d, c, ...} ordered by (f, d, c) like Python tuples (c is unique)
function heapLess(x, y) { return x.f < y.f || (x.f === y.f && (x.d < y.d || (x.d === y.d && x.c < y.c))); }
function heapPush(h, e) {
    h.push(e); let i = h.length - 1;
    while (i > 0) { const p = (i - 1) >> 1; if (!heapLess(h[i], h[p])) break; const t = h[i]; h[i] = h[p]; h[p] = t; i = p; }
}
function heapPop(h) {
    const top = h[0], last = h.pop();
    if (h.length) {
        h[0] = last; let i = 0;
        while (true) {
            const l = 2 * i + 1, r = l + 1; let m = i;
            if (l < h.length && heapLess(h[l], h[m])) m = l;
            if (r < h.length && heapLess(h[r], h[m])) m = r;
            if (m === i) break;
            const t = h[i]; h[i] = h[m]; h[m] = t; i = m;
        }
    }
    return top;
}

/** the list of a parent-linked path {k, up} (null = empty), root first */
function unlinkPath(node) { const out = []; for (; node; node = node.up) out.push(node.k); return out.reverse(); }

/** a mutation sequence taking B to an acyclic quiver, recovered from a c-vector certificate (best-first search on
 *  sum |C_ij| over the extended exchange matrix [B; C]). -> [path, acyclic quiver reached]. */
function mutationPath(B, cert) {
    const n = B.length, sigma = cert.order, V = cert.c_vectors, C = zeros(n);
    for (let a = 0; a < n; a++) for (let i = 0; i < n; i++) C[i][sigma[a]] = V[a][i];
    const key = (X, Y) => X.map(r => r.join(',')).join(';') + '|' + Y.map(r => r.join(',')).join(';');
    const norm = Y => { let s = 0n; for (const r of Y) for (const x of r) s += babs(x); return s; };
    // paths are kept as parent-linked lists (the same paths as the reference's path + [k], in linear memory)
    const heap = [{ f: norm(C), d: 0, c: 0, B: B, C: C, path: null }], seen = new Set([key(B, C)]); let cnt = 0;
    while (heap.length) {
        const e = heapPop(heap);
        if (isAcyclic(e.B)) return [unlinkPath(e.path), e.B];
        for (let k = 0; k < n; k++) {
            const bc = extendedMutate(e.B, e.C, k), kk = key(bc[0], bc[1]);
            if (seen.has(kk)) continue;
            seen.add(kk); cnt += 1;
            heapPush(heap, { f: norm(bc[1]), d: e.d + 1, c: cnt, B: bc[0], C: bc[1], path: { k: k, up: e.path } });
        }
    }
    throw new Error('no acyclic quiver reached; the certificate is not valid');
}

// =====================================================================================================================
// independent certificate check
// =====================================================================================================================

function isRealRoot(v, S0) {
    const n = v.length; v = v.slice();
    if (!v.some(x => x !== 0n)) return false;
    if (v.every(x => x <= 0n)) v = v.map(x => -x);
    if (!v.every(x => x >= 0n)) return false;
    let q = 0n;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) q += v[i] * S0[i][j] * v[j];
    if (q !== 2n) return false;
    const sum = () => v.reduce((s, x) => s + x, 0n);
    while (sum() > 1n) {
        let found = false;
        for (let i = 0; i < n; i++) {
            let a = 0n;
            for (let j = 0; j < n; j++) a += S0[i][j] * v[j];
            if (a > 0n) {
                v[i] -= a;
                if (v[i] < 0n) return false;
                found = true; break;
            }
        }
        if (!found) return false;
    }
    return true;
}

function reflMatrix(v, S0) {
    const n = v.length, Sv = range(n).map(i => { let s = 0n; for (let j = 0; j < n; j++) s += S0[i][j] * v[j]; return s; });
    return range(n).map(i => range(n).map(j => (i === j ? 1n : 0n) - v[i] * Sv[j]));
}

/** exact check of a certificate, independent of the search. -> [ok, message]. */
function verifyCertificate(B, cert) {
    const n = B.length, kind = cert.kind;
    if (kind === 'acyclic-input') return [isAcyclic(B), isAcyclic(B) ? 'input is acyclic' : 'input is not acyclic'];
    if (kind === 'mutation-path') {
        let X = copyMat(B);
        for (const k of cert.path) X = mutate(X, k);
        const ok = isAcyclic(X) && matEq(X, cert.acyclic);
        return [ok, ok ? 'mutation sequence ends at an acyclic quiver' : 'mutation sequence check FAILED'];
    }
    if (kind !== 'c-vectors') return [false, 'unknown certificate kind'];
    const sigma = cert.order.slice(), B0 = cert.acyclic, V = cert.c_vectors;
    if (sigma.slice().sort((x, y) => x - y).join(',') !== range(n).join(',')) return [false, 'order is not a permutation'];
    try { checkSkew(B0); } catch (e) { return [false, 'acyclic quiver: ' + e.message]; }
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (B0[i][j] < 0n) return [false, 'acyclic quiver not topologically labelled'];
    const U0 = companion(B0, range(n)), S0 = sym(U0), signs = [];
    for (const v of V) {
        const any = v.some(x => x !== 0n);
        if (any && v.every(x => x >= 0n)) signs.push(1);
        else if (any && v.every(x => x <= 0n)) signs.push(-1);
        else return [false, 'a c-vector is not sign-coherent'];
        if (!isRealRoot(v, S0)) return [false, 'a c-vector is not a real root'];
    }
    const det = fracDet(V);
    if (!(det.d === 1n && babs(det.n) === 1n)) return [false, 'c-vectors are not a unimodular basis'];
    const form = (M, x, y) => { let s = 0n; for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) s += x[i] * M[i][j] * y[j]; return s; };
    for (let a = 0; a < n; a++)
        for (let b = a + 1; b < n; b++)
            if (signs[a] === signs[b] && form(S0, V[a], V[b]) > 0n) return [false, 'ST condition (2) fails'];
    const order = range(n).filter(k => signs[k] === 1).concat(range(n).filter(k => signs[k] === -1));
    let P = identity(n);
    for (const k of order) P = matMul(P, reflMatrix(V[k], S0));
    let E = identity(n);
    for (let i = 0; i < n; i++) E = matMul(E, reflMatrix(range(n).map(j => j === i ? 1n : 0n), S0));
    if (!matEq(P, E)) return [false, 'ST condition (3) fails'];
    for (let a = 0; a < n; a++)
        for (let b = 0; b < n; b++)
            if (form(U0, V[b], V[a]) - form(U0, V[a], V[b]) !== B[sigma[a]][sigma[b]]) return [false, 'exchange matrix mismatch'];
    if (cert.path !== undefined) {
        let X = copyMat(B);
        for (const k of cert.path) X = mutate(X, k);
        if (!(isAcyclic(X) && matEq(X, cert.path_end))) return [false, 'mutation sequence check FAILED'];
    }
    return [true, 'c-vectors of a seed of the acyclic quiver with exchange matrix B (Speyer-Thomas Thm 1.4 + Thm 7.2)'];
}

// =====================================================================================================================
// finite type, caps, main entry points
// =====================================================================================================================

/** a canonical form of the quiver B under relabelling (a string): colour refinement (by colours and arrow weights of
 *  the neighbours) plus individualization of the first non-singleton cell, minimised over the branches (a small
 *  version of the method of nauty). Equal for isomorphic quivers, distinct otherwise. Same procedure as the Python
 *  reference's canonical_form. */
function canonicalForm(B) {
    const n = B.length, W = B.map(r => r.map(x => Number(x)));
    const cmpPair = (p, q) => (p[0] - q[0]) || (p[1] - q[1]);
    const cmpSig = (s, t) => {                        // Python tuple order on (colour, sorted neighbour pairs)
        if (s[0] !== t[0]) return s[0] - t[0];
        const a = s[1], b = t[1];
        for (let i = 0; i < a.length && i < b.length; i++) { const c = cmpPair(a[i], b[i]); if (c) return c; }
        return a.length - b.length;
    };
    const nclasses = col => new Set(col).size;
    const refine = col => {
        while (true) {
            const sig = [];
            for (let v = 0; v < n; v++) {
                const nb = [];
                for (let w = 0; w < n; w++) if (W[v][w] !== 0) nb.push([col[w], W[v][w]]);
                nb.sort(cmpPair);
                sig.push([col[v], nb]);
            }
            const idx = range(n).sort((x, y) => cmpSig(sig[x], sig[y]));
            const nw = new Array(n); let rank = -1;
            for (let i = 0; i < n; i++) {
                if (i === 0 || cmpSig(sig[idx[i - 1]], sig[idx[i]]) !== 0) rank++;
                nw[idx[i]] = rank;
            }
            if (nclasses(nw) === nclasses(col)) return nw;
            col = nw;
        }
    };
    let best = null;
    const search = col => {
        col = refine(col);
        if (nclasses(col) === n) {
            const order = range(n).sort((x, y) => col[x] - col[y]), t = [];
            for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) t.push(W[order[i]][order[j]]);
            if (best === null || tupleCmp(t, best) < 0) best = t;
            return;
        }
        const cnt = new Map();
        for (const x of col) cnt.set(x, (cnt.get(x) || 0) + 1);
        let c = null;
        for (const [x, k] of cnt) if (k > 1 && (c === null || x < c)) c = x;
        for (let v = 0; v < n; v++) {
            if (col[v] !== c) continue;
            search(col.map((x, w) => 2 * x + ((x > c || (x === c && w !== v)) ? 1 : 0)));
        }
    };
    search(new Array(n).fill(0));
    return best.join(',');
}

/** breadth-first search, up to isomorphism, over the quivers with all |b_ij| <= 2 that are mutation equivalent to B
 *  through such quivers (a finite set). -> [path, acyclic quiver] or null. Complete for finite mutation type (FST):
 *  acyclicity is invariant under relabelling, and mutations of isomorphic quivers are isomorphic. */
function finiteSearch(B) {
    const n = B.length;
    const seen = new Set([canonicalForm(B)]), dq = [[B, null]]; let head = 0;   // paths parent-linked
    while (head < dq.length) {
        const X = dq[head][0], path = dq[head][1]; dq[head] = null; head++;
        if (isAcyclic(X)) return [unlinkPath(path), X];
        for (let k = 0; k < n; k++) {
            const Y = mutate(X, k);
            if (maxAbs(Y) > 2n) continue;
            const ky = canonicalForm(Y);
            if (!seen.has(ky)) { seen.add(ky); dq.push([Y, { k: k, up: path }]); }
        }
    }
    return null;
}

/** integer upper bounds for N_* and E_* (write-up, Lemma 'Uniform caps'). */
function uniformCaps(n, beta) {
    const N = BigInt(n), A = 1n + beta, Lam = N * A ** N, X1 = factorial(n - 1) * (2n * Lam) ** (N - 1n);
    const AQ = 2n * (isqrt(Lam) + 1n), LamQ = N * AQ ** N, X2 = factorial(n - 1) * (2n * LamQ) ** (N - 1n);
    const X3 = N * AQ * X2, X4 = N * N * AQ * X2 ** 2n;
    const invXi = (N * N * A ** (N - 1n) * X1 ** 2n) ** (N - 1n), invNu = X3 ** (2n * (N - 1n)) * X4;
    const invDelta = 2n * (2n * N + 1n) * (Lam + 1n) ** N, H = 2n * Lam * X1;
    const R = H * invDelta * (isqrt(invXi * invNu) + 1n);
    return [N * (1n + R) ** N, factorial(n) * R ** N];
}

/** the uniform caps (N_*, E_*) of uniformCaps, computed exactly only if a comparison needs them (as in the Rust port).
 *  For n >= 16 they have more than 2^20 bits, which is more than Firefox allows for a BigInt ("BigInt is too large to
 *  allocate"), and computing them is slow anyway. The descents compare against them through rigorous lower bounds
 *  on log2 (the same formulas with bit lengths: lg(x) = bits(x) - 1 <= log2 x, isqrt(x) + 1 >= sqrt(x),
 *  (x + 1)^k >= x^k), and the exact values are only computed if a step count or an entry gets that large. */
class Caps {
    constructor(n, beta) {
        this.n = n; this.beta = beta; this._exact = null;
        const lg = x => bitLength(x) - 1, N = n;
        const la = lg(1n + beta), ln = lg(BigInt(n)), lf1 = lg(factorial(n - 1));
        const llam = ln + N * la, lx1 = lf1 + (N - 1) * (1 + llam), laq = 1 + Math.floor(llam / 2);
        const llamq = ln + N * laq, lx2 = lf1 + (N - 1) * (1 + llamq), lx3 = ln + laq + lx2, lx4 = 2 * ln + laq + 2 * lx2;
        const linvXi = (N - 1) * (2 * ln + (N - 1) * la + 2 * lx1), linvNu = 2 * (N - 1) * lx3 + lx4;
        const linvDelta = 1 + lg(BigInt(2 * n + 1)) + N * llam, lh = 1 + llam + lx1;
        const lr = lh + linvDelta + Math.floor((linvXi + linvNu) / 2);
        this.nLg = ln + N * lr; this.eLg = lg(factorial(n)) + N * lr;          // N_* >= 2^nLg, E_* >= 2^eLg
    }
    exact() { if (!this._exact) this._exact = uniformCaps(this.n, this.beta); return this._exact; }
    /** steps < N_* */
    stepsBelow(steps) { return Math.floor(Math.log2(steps + 1)) + 1 <= this.nLg || BigInt(steps) < this.exact()[0]; }
    /** x > E_* (x >= 0) */
    above(x) { return bitLength(x) > this.eLg && x > this.exact()[1]; }
}

// =====================================================================================================================
// Theorem P orders and rigorous NO filters (writeup Section 7, Corollary 7.4)
// =====================================================================================================================

function maxAbs(B) { let m = 0n; for (const r of B) for (const x of r) { const a = babs(x); if (a > m) m = a; } return m; }
function sumAbs(B) { let s = 0n; for (const r of B) for (const x of r) s += babs(x); return s; }
function submatrix(B, S) { return S.map(i => S.map(j => B[i][j])); }
function pyTuple(v) { return '(' + v.join(', ') + (v.length === 1 ? ',' : '') + ')'; }   // Python str(tuple)
function pyList(v) { return '[' + v.join(', ') + ']'; }                                  // Python str(list)
function pyFloorDiv(a, b) {                           // Python a // b for BigInts
    const q = a / b;
    return (a % b !== 0n && ((a < 0n) !== (b < 0n))) ? q - 1n : q;
}

/** k-subsets of [0..n-1] in lexicographic order, like itertools.combinations(range(n), k). */
function* combinations(n, k) {
    if (k > n) return;
    const c = range(k);
    while (true) {
        yield c.slice();
        let i = k;
        while (i > 0 && c[i - 1] === n - k + i - 1) i--;
        if (i === 0) return;
        c[i - 1]++;
        for (let j = i; j < k; j++) c[j] = c[j - 1] + 1;
    }
}

/** chordless cycles (length >= 3) of the underlying simple graph, each as a vertex list in traversal order. */
function chordlessCycles(B) {
    const n = B.length, out = [];
    for (let k = 3; k <= n; k++) {
        for (const S of combinations(n, k)) {
            let bad = false;
            for (const a of S) {
                let d = 0;
                for (const b of S) if (b !== a && B[a][b] !== 0n) d++;
                if (d !== 2) { bad = true; break; }
            }
            if (bad) continue;
            const cyc = [S[0]]; let prev = -1;
            while (cyc.length < k) {
                const last = cyc[cyc.length - 1];
                let nxt = -1;
                for (const b of S) if (B[last][b] !== 0n && b !== prev && !cyc.includes(b)) { nxt = b; break; }
                if (nxt < 0) break;
                prev = last; cyc.push(nxt);
            }
            if (cyc.length === k && B[cyc[k - 1]][cyc[0]] !== 0n) out.push(cyc);
        }
    }
    return out;
}

/** order in Lambda(B): every chordless cycle has winding number 1 (oriented, traversed along its arrows) or 0. */
function inLambda(B, order, cycles) {
    const pos = new Map(); order.forEach((v, i) => pos.set(v, i));
    for (const cyc of (cycles === undefined ? chordlessCycles(B) : cycles)) {
        const k = cyc.length; let w = 0, fwd = true, bwd = true;
        for (let i = 0; i < k; i++) {
            const a = cyc[i], b = cyc[(i + 1) % k], x = B[a][b];
            if (x > 0n && pos.get(a) > pos.get(b)) w++;
            if (x < 0n && pos.get(a) < pos.get(b)) w--;
            if (!(x > 0n)) fwd = false;
            if (!(x < 0n)) bwd = false;
        }
        if (w !== (fwd ? 1 : (bwd ? -1 : 0))) return false;
    }
    return true;
}

function orientationKey(B, lam) {
    const n = B.length, pos = new Array(n); lam.forEach((v, i) => { pos[v] = i; });
    const out = [];
    for (let v = 0; v < n; v++) for (let w = 0; w < n; w++) if (B[v][w] !== 0n && pos[v] < pos[w]) out.push(v + '>' + w);
    return out.join(',');
}

/** one order in Lambda(B), or null: insert vertices one at a time into a cyclic order, pruning as soon as a chordless
 *  cycle with all its vertices placed has the wrong winding number (it depends only on their cyclic order). */
function lambdaElement(B, cycles) {
    const n = B.length, order = [], seen = new Set(); let queue = [0];
    while (order.length < n) {                         // BFS order, so that cycles close early
        if (!queue.length) { let m = -1; for (let v = 0; v < n; v++) if (!seen.has(v)) { m = v; break; } queue = [m]; }
        const v = queue.shift();
        if (seen.has(v)) continue;
        seen.add(v); order.push(v);
        for (let w = 0; w < n; w++) if (B[v][w] !== 0n && !seen.has(w)) queue.push(w);
    }
    const closes = range(n).map(k => cycles.filter(c => c.includes(order[k]) && c.every(x => order.indexOf(x) <= k)));
    const rec = (k, cyc) => {
        if (k === n) return cyc;
        const v = order[k];
        for (let p = 1; p <= cyc.length; p++) {
            const c2 = cyc.slice(0, p).concat([v], cyc.slice(p));
            if (closes[k].every(c => inLambda(B, c2.filter(x => c.includes(x)), [c]))) {
                const r = rec(k + 1, c2);
                if (r) return r;
            }
        }
        return null;
    };
    return rec(1, [order[0]]);
}

/** one linear order from each class of Lambda(B) under exchanges of adjacent vertices not joined by an arrow (a class =
 *  the acyclic orientation the order induces), sorted. Empty iff B has no totally proper cyclic ordering.
 *  n <= bruteForceMax: enumerate all (n-1)! cyclic orders. Larger n: one element by pruned insertion, then the rest by
 *  source-to-sink flips (complete by Pretzel 1986: the winding numbers fix the circulations). */
function lambdaClasses(B, bruteForceMax) {
    if (bruteForceMax === undefined) bruteForceMax = 8;
    const n = B.length, cycles = chordlessCycles(B), seen = new Map();
    if (n <= bruteForceMax) {
        for (const rest of permutations(range(n).slice(1))) {
            const o = [0].concat(rest);
            if (!inLambda(B, o, cycles)) continue;
            for (let r = 0; r < n; r++) {
                const lam = o.slice(r).concat(o.slice(0, r)), key = orientationKey(B, lam);
                if (!seen.has(key)) seen.set(key, lam);
            }
        }
        return Array.from(seen.values()).sort(tupleCmp);
    }
    const lam0 = lambdaElement(B, cycles);
    if (lam0 === null) return [];
    seen.set(orientationKey(B, lam0), lam0); const stack = [lam0];
    while (stack.length) {
        const lam = stack.pop(), pos = new Array(n); lam.forEach((v, i) => { pos[v] = i; });
        for (const x of lam) {                        // x a source of the orientation: no neighbour before it
            let src = true;
            for (let w = 0; w < n; w++) if (B[x][w] !== 0n && !(pos[w] > pos[x])) { src = false; break; }
            if (!src) continue;
            const nw = lam.filter(v => v !== x).concat([x]), key = orientationKey(B, nw);
            if (!seen.has(key)) { seen.set(key, nw); stack.push(nw); }
        }
    }
    return Array.from(seen.values()).sort(tupleCmp);
}

/** 3-vertex quiver mutation-cyclic? (Beineke-Bruestle-Hille: cyclic, all weights >= 2, Markov constant <= 4) */
function bbhMutationCyclic(B3) {
    let x = B3[0][1], y = B3[1][2], z = B3[2][0];
    if (!((x > 0n && y > 0n && z > 0n) || (x < 0n && y < 0n && z < 0n))) return false;
    x = babs(x); y = babs(y); z = babs(z);
    return x >= 2n && y >= 2n && z >= 2n && x * x + y * y + z * z - x * y * z <= 4n;
}

/** a full subquiver that is not mutation-acyclic (then neither is B, by [BMR]); -> [vertices, how] or null. Size 3
 *  uses the Beineke-Bruestle-Hille criterion; larger sizes use decide() recursively ('auto', no certificate re-check,
 *  shared caches). */
function subquiverFilter(B, sizes) {
    const n = B.length;
    for (const k of sizes) {
        if (k >= n) continue;
        for (const S of combinations(n, k)) {
            const Bs = submatrix(B, S);
            if (k === 3) {
                if (bbhMutationCyclic(Bs)) return [S, 'Markov triangle (BBH)'];
            } else if (isConnected(Bs) && !isAcyclic(Bs)) {
                if (decideBig(Bs, 'auto', false, null).answer === 'NO') return [S, 'decided NO'];
            }
        }
    }
    return null;
}

/** the full subquiver on verts is acyclic */
function acyclicOn(B, verts) {
    const rem = verts.slice();
    while (rem.length) {
        let p = -1;
        for (let i = 0; i < rem.length && p < 0; i++) {
            let ok = true;
            for (const w of rem) if (B[w][rem[i]] > 0n) { ok = false; break; }
            if (ok) p = i;
        }
        if (p < 0) return false;
        rem.splice(p, 1);
    }
    return true;
}

function insOuts(B, v) {
    const n = B.length, ins = [], outs = [];
    for (let a = 0; a < n; a++) { if (B[a][v] > 0n) ins.push(a); if (B[v][a] > 0n) outs.push(a); }
    return [ins, outs];
}

/** a vertex v whose in- or out-neighbourhood induces a quiver with an oriented cycle, or null. Such B is not
 *  mutation-acyclic [Ne, Thm 4.4] (cf. Warkentin's thesis, Rem 2.2). */
function vortexFilter(B) {
    for (let v = 0; v < B.length; v++) {
        const io = insOuts(B, v);
        if (!acyclicOn(B, io[0]) || !acyclicOn(B, io[1])) return v;
    }
    return null;
}

/** the point of return r if B is a fork in Warkentin's sense (Def 2.1 of his thesis), else null. */
function forkPoint(B) {
    const n = B.length;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) if (i !== j && babs(B[i][j]) < 2n) return null;
    for (let r = 0; r < n; r++) {
        const io = insOuts(B, r), ins = io[0], outs = io[1];
        if (!ins.length || !outs.length) continue;
        let ok = true;
        for (const i of ins) { for (const j of outs) if (!(B[j][i] > B[i][r] && B[j][i] > B[r][j])) { ok = false; break; } if (!ok) break; }
        if (ok && acyclicOn(B, ins) && acyclicOn(B, outs)) return r;
    }
    return null;
}

function matKey(X) { return X.map(r => r.join(',')).join(';'); }

/** YES fast path (docs/moonshots/forks): unfork by mutating at points of return, then a best-first search through
 *  non-forks with max|b| at most that of the unforked quiver. -> [path, acyclic quiver] or null (inconclusive).
 *  Any path found is an explicit certificate, so this never affects correctness. */
function combinatorialYes(B, budget) {
    if (budget === undefined) budget = 400;
    const path = []; let X = B; const cap = sumAbs(B) + 10n;
    while (BigInt(path.length) < cap) {
        const r = forkPoint(X);
        if (r === null) break;
        const X2 = mutate(X, r);
        if (forkPoint(X2) === r) return null;         // a centre: every quiver in the class is a fork
        X = X2; path.push(r);
    }
    const m = maxAbs(X), n = B.length, seen = new Set([matKey(X)]);
    const heap = [{ f: sumAbs(X), d: 0, c: 0, Y: X, p: [] }]; let cnt = 0;
    while (heap.length && cnt < budget) {
        const e = heapPop(heap); cnt += 1;
        if (isAcyclic(e.Y)) return [path.concat(e.p), e.Y];
        for (let k = 0; k < n; k++) {
            const Z = mutate(e.Y, k), kz = matKey(Z);
            if (seen.has(kz) || maxAbs(Z) > m || forkPoint(Z) !== null) continue;
            seen.add(kz); heapPush(heap, { f: sumAbs(Z), d: cnt * n + k + 1, c: 0, Y: Z, p: e.p.concat([k]) });
        }
    }
    return null;
}

/** determinant of an integer matrix (fraction-free Bareiss elimination, as in the reference). */
function detInt(A) {
    A = A.map(r => r.slice()); const n = A.length; let sgn = 1n, prev = 1n;
    for (let k = 0; k < n - 1; k++) {
        if (A[k][k] === 0n) {
            let found = false;
            for (let i = k + 1; i < n; i++) if (A[i][k] !== 0n) { const t = A[k]; A[k] = A[i]; A[i] = t; sgn = -sgn; found = true; break; }
            if (!found) return 0n;
        }
        for (let i = k + 1; i < n; i++)
            for (let j = k + 1; j < n; j++) A[i][j] = pyFloorDiv(A[i][j] * A[k][k] - A[i][k] * A[k][j], prev);
        prev = A[k][k];
    }
    return sgn * A[n - 1][n - 1];
}

/** connected acyclic quivers with Coxeter polynomial f (Lemma candidate), by branch and bound on Neville's formula
 *  M_Q = n - a_1 = sum_{i<j} b_ij P_ij (P = (I - N)^-1, topological labels). -> list of upper tuples, or null if the
 *  node budget runs out (then the filter is inconclusive). */
function coxeterCandidates(f, nodeBudget) {
    if (nodeBudget === undefined) nodeBudget = 300000;
    const n = f.length - 1, Mval = BigInt(n) - f[n - 1], pts = [1n, -1n, 2n, -2n, 3n];
    const vals = pts.map(x => { let s = 0n, xi = 1n; for (const c of f) { s += c * xi; xi *= x; } return s; });
    const pairs = [];
    for (let j = 1; j < n; j++) for (let i = j - 1; i >= 0; i--) pairs.push([i, j]);
    const b = zeros(n), P = identity(n), out = []; let nodes = 0;
    const OVER = {};
    const test = () => {
        const Bq = range(n).map(i => range(n).map(j => i !== j ? (i < j ? b[i][j] : -b[j][i]) : 0n));
        if (!isConnected(Bq)) return false;
        const U = companion(Bq, range(n));
        for (let t = 0; t < pts.length; t++) {
            const x = pts[t], M = range(n).map(i => range(n).map(j => x * U[i][j] + U[j][i]));
            if (detInt(M) !== vals[t]) return false;
        }
        const g = flAdjugate(coxeter(U))[0];
        return g.length === f.length && g.every((c, i) => c === f[i]);
    };
    const rec = (idx, msum) => {
        nodes += 1;
        if (nodes > nodeBudget) throw OVER;
        if (idx === pairs.length) {
            if (msum === Mval && test()) { const t = []; for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) t.push(b[i][j]); out.push(t); }
            return;
        }
        const i = pairs[idx][0], j = pairs[idx][1]; let base = 0n;
        for (let k = i + 1; k < j; k++) base += P[i][k] * b[k][j];
        let w = 0n;
        while (msum + w * (w + base) <= Mval) {
            b[i][j] = w; P[i][j] = w + base; rec(idx + 1, msum + w * (w + base)); w += 1n;
        }
        b[i][j] = 0n; P[i][j] = 0n;
    };
    try { rec(0, 0n); } catch (e) { if (e === OVER) return null; throw e; }
    return out;
}

/** CPython 3.12's list.sort for short lists (count_run, then binary insertion), with the same sequence of comparisons
 *  lt(x, y) (x < y): the comparisons decide signs in Q(rho), so their order fixes the refinement levels of rho. */
function pySort(v, lt) {
    const n = v.length;
    if (n < 2) return;
    let r = 2;
    if (lt(v[1], v[0])) {
        while (r < n && lt(v[r], v[r - 1])) r++;
        for (let a = 0, z = r - 1; a < z; a++, z--) { const t = v[a]; v[a] = v[z]; v[z] = t; }
    } else {
        while (r < n && !lt(v[r], v[r - 1])) r++;
    }
    for (let st = r; st < n; st++) {
        const pivot = v[st]; let l = 0, rr = st;
        do {
            const p = l + ((rr - l) >> 1);
            if (lt(pivot, v[p])) rr = p; else l = p + 1;
        } while (l < rr);
        v.splice(st, 1); v.splice(l, 0, pivot);
    }
}

/** G(sigma) != empty set, where G(sigma) = {theta > 0 : eps(theta) has no zero and StOk(U, +-eps(theta))} and
 *  eps_k(theta) = sgn(theta lam_+(e_k) + lam_-(e_k)). By Theorem W(a) (lem:gset), an order with G(sigma) empty never
 *  certifies. */
function gSetNonempty(od) {
    const R = od.R, n = od.n, U = od.U, lp = od.lp, lm = od.lm;
    const sp = lp.map(x => R.sign(x)), sm = lm.map(x => R.sign(x));
    if (sp.includes(0) || sm.includes(0)) return false;
    const pos = range(n).filter(k => sp[k] !== sm[k]);     // breakpoints theta_k = -lam_-(e_k)/lam_+(e_k) > 0
    const cmp = (a, b) => R.sign(R.reduce(psub(pmul(lm[b], lp[a]), pmul(lm[a], lp[b])))) * sp[a] * sp[b];   // sign(theta_a - theta_b)
    pySort(pos, (a, b) => cmp(a, b) < 0);
    const groups = [];
    for (const k of pos) {
        if (groups.length && cmp(groups[groups.length - 1][0], k) === 0) groups[groups.length - 1].push(k);
        else groups.push([k]);
    }
    const inPos = range(n).map(k => pos.includes(k)), below = new Array(n).fill(false);   // breakpoints below theta
    for (let i = 0; i <= groups.length; i++) {
        if (i) for (const k of groups[i - 1]) below[k] = true;
        const eps = range(n).map(k => (!inPos[k] || below[k]) ? sp[k] : -sp[k]);
        if (stOk(U, eps) || stOk(U, eps.map(e => -e))) return true;
    }
    return false;
}

/** descent at (order, s) in chunks, then the axis walk. Returns ['cert', cert] | ['bad', why] | ['cap', null].
 *  'bad' outcomes cannot occur at a seed order for generic s, and at most n values of s^2 are non-generic. */
function* orderTask(od, s, caps, chunk) {
    const dg = yield* descentGen(od, s, caps, chunk), kind = dg[0], G = dg[1];
    if (kind === 'cap') return ['cap', null];
    if (kind !== 'obtuse') return ['bad', kind];
    const cert = walk(od, G, s);
    return cert ? ['cert', cert] : ['bad', 'walk'];
}

// =====================================================================================================================
// polynomial-time selection of the class (SELECT; writeup Section 7; docs/moonshots/select, audit2)
// =====================================================================================================================

function bfsParents(B) {                              // BFS tree from vertex 0: parent array (-1 = root/unreached), visit order
    const n = B.length, par = new Array(n).fill(-2), order = [0], q = [0]; par[0] = -1; let h = 0;
    while (h < q.length) {
        const x = q[h++];
        for (let y = 0; y < n; y++) if (B[x][y] !== 0n && par[y] === -2) { par[y] = x; q.push(y); order.push(y); }
    }
    return [par, order];
}

function bitLen(x) { return x === 0n ? 0 : x.toString(2).length; }

/** a basis of the cycle space over GF(2) consisting of chordless cycles (B connected): the fundamental cycles of a BFS
 *  tree, each repeatedly replaced by a strictly shorter chordless half that keeps the family independent. */
function chordlessCycleBasis(B) {
    const n = B.length, po = bfsParents(B), par = po[0], order = po[1], depth = new Array(n).fill(0);
    for (const v of order.slice(1)) depth[v] = depth[par[v]] + 1;
    const treePath = (a, b) => {
        const pa = [a], pb = [b];
        while (pa[pa.length - 1] !== pb[pb.length - 1]) {
            if (depth[pa[pa.length - 1]] >= depth[pb[pb.length - 1]]) pa.push(par[pa[pa.length - 1]]);
            else pb.push(par[pb[pb.length - 1]]);
        }
        return pa.concat(pb.slice(0, pb.length - 1).reverse());
    };
    const isTree = (a, b) => par[a] === b || par[b] === a;
    const eidx = new Map(), edges = [];
    for (let a = 0; a < n; a++) for (let b = a + 1; b < n; b++) if (B[a][b] !== 0n) { eidx.set(a * n + b, edges.length); edges.push([a, b]); }
    const vec = cyc => {
        let v = 0n;
        for (let i = 0; i < cyc.length; i++) {
            const x = cyc[i], y = cyc[(i + 1) % cyc.length];
            v ^= 1n << BigInt(eidx.get(Math.min(x, y) * n + Math.max(x, y)));
        }
        return v;
    };
    const independent = vs => {
        const piv = new Map();
        for (let r of vs) {
            const keys = Array.from(piv.keys()).sort((x, y) => y - x);
            for (const p of keys) if ((r >> BigInt(p)) & 1n) r ^= piv.get(p);
            if (r === 0n) return false;
            piv.set(bitLen(r) - 1, r);
        }
        return true;
    };
    const fam = [];
    for (const e of edges) if (!isTree(e[0], e[1])) fam.push(treePath(e[0], e[1]));
    let vecs = fam.map(vec);
    for (let idx = 0; idx < fam.length; idx++) {
        while (true) {
            const cyc = fam[idx], k = cyc.length; let chord = null;
            for (let i = 0; i < k && !chord; i++)
                for (let j = i + 2; j < k; j++)
                    if (!(i === 0 && j === k - 1) && B[cyc[i]][cyc[j]] !== 0n) { chord = [i, j]; break; }
            if (!chord) break;
            const i = chord[0], j = chord[1], h1 = cyc.slice(i, j + 1), h2 = cyc.slice(j).concat(cyc.slice(0, i + 1));
            const v1 = vecs.slice(0, idx).concat([vec(h1)], vecs.slice(idx + 1));
            if (independent(v1)) { fam[idx] = h1; vecs = v1; }
            else { fam[idx] = h2; vecs[idx] = vec(h2); }
        }
    }
    return fam;
}

/** a linear order whose closure has winding number 1 on every oriented and 0 on every non-oriented chordless cycle,
 *  found in polynomial time (audit2 fix 5; the linear program of [FN, Thm 2.16] as difference constraints), B
 *  connected. -> order, or null, which proves Lambda(B) empty. If Lambda(B) is not empty, the order lies in Lambda(B).
 *  Solve over Q for an integer cochain k (zero on a BFS tree) with the target windings on a chordless GF(2)-basis
 *  (a non-integral k means Lambda(B) is empty); then integers Y with 1 <= Y_v - Y_u + N k_e <= N - 1 for every arrow
 *  e = u->v (N = n + 1) by Bellman-Ford; sort the vertices by Y mod N. */
function windingOrder(B) {
    const n = B.length, par = bfsParents(B)[0];
    const arrows = [];
    for (let u = 0; u < n; u++) for (let v = 0; v < n; v++) if (B[u][v] > 0n) arrows.push([u, v]);
    const col = new Map();                            // non-tree arrow u->v (key u*n+v) -> column
    for (const a of arrows) if (par[a[1]] !== a[0] && par[a[0]] !== a[1]) col.set(a[0] * n + a[1], col.size);
    const m = col.size, rows = [];
    for (const cyc of chordlessCycleBasis(B)) {
        const k = cyc.length, r = new Array(m + 1).fill(Q0); let fwd = true, bwd = true;
        for (let i = 0; i < k; i++) {
            const a = cyc[i], b = cyc[(i + 1) % k];
            if (B[a][b] > 0n && col.has(a * n + b)) { const c = col.get(a * n + b); r[c] = qadd(r[c], Q1); }
            else if (B[a][b] < 0n && col.has(b * n + a)) { const c = col.get(b * n + a); r[c] = qsub(r[c], Q1); }
            if (!(B[a][b] > 0n)) fwd = false;
            if (!(B[a][b] < 0n)) bwd = false;
        }
        r[m] = qi(fwd ? 1n : (bwd ? -1n : 0n));
        rows.push(r);
    }
    for (let c = 0; c < m; c++) {                     // Gauss-Jordan over Q (the matrix is invertible)
        let p = -1;
        for (let i = c; i < m; i++) if (!qzero(rows[i][c])) { p = i; break; }
        if (p < 0) throw new Error('winding_order: singular system');
        const t = rows[c]; rows[c] = rows[p]; rows[p] = t;
        const piv = rows[c][c]; rows[c] = rows[c].map(x => qdiv(x, piv));
        for (let i = 0; i < m; i++) {
            if (i !== c && !qzero(rows[i][c])) { const f = rows[i][c], rc = rows[c]; rows[i] = rows[i].map((x, j) => qsub(x, qmul(f, rc[j]))); }
        }
    }
    const kc = range(m).map(c => rows[c][m]);
    if (kc.some(x => x.d !== 1n)) return null;
    const N = BigInt(n + 1), cons = [];               // [u, v, w]: Y_v <= Y_u + w
    for (const a of arrows) {
        const u = a[0], v = a[1], ke = col.has(u * n + v) ? kc[col.get(u * n + v)].n : 0n;
        cons.push([u, v, N * (1n - ke) - 1n]); cons.push([v, u, N * ke - 1n]);
    }
    const Y = new Array(n).fill(0n);
    for (let it = 0; it <= n; it++) {
        let changed = false;
        for (const c of cons) if (Y[c[0]] + c[2] < Y[c[1]]) { Y[c[1]] = Y[c[0]] + c[2]; changed = true; }
        if (!changed) break;
        if (it === n) return null;                    // a negative cycle: no order has these windings
    }
    const md = v => ((Y[v] % N) + N) % N;
    return range(n).sort((x, y) => { const a = md(x), b = md(y); return a < b ? -1 : (a > b ? 1 : x - y); });
}

/** the acyclic orientation induced by a linear order, as a boolean matrix O[x][y] (arrow x -> y of the graph). */
function orientation(B, order) {
    const n = B.length, pos = new Array(n); order.forEach((v, i) => { pos[v] = i; });
    return range(n).map(x => range(n).map(y => B[x][y] !== 0n && pos[x] < pos[y]));
}

/** the lexicographically smallest linear order inducing the acyclic orientation O, or null if O has a cycle. */
function linearExtension(n, O) {
    const indeg = new Array(n).fill(0), done = new Array(n).fill(false), res = [];
    for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (O[a][b]) indeg[b]++;
    while (true) {
        let v = -1;
        for (let x = 0; x < n; x++) if (!done[x] && indeg[x] === 0) { v = x; break; }
        if (v < 0) break;
        done[v] = true; res.push(v);
        for (let b = 0; b < n; b++) if (O[v][b]) indeg[b]--;
    }
    return res.length === n ? res : null;
}

/** k with k(x) - k(y) in {0, 1} on the arrows x -> y of O0 and O = O0 with the arrows where it is 1 reversed, i.e. O
 *  is in the source-to-sink flip class of O0 (B connected); null if there is no such k. */
function flipPotential(B, O0, O) {
    const n = B.length, k = new Array(n).fill(null), st = [0]; k[0] = 0; let cnt = 1;
    while (st.length) {
        const x = st.pop();
        for (let y = 0; y < n; y++) {
            if (B[x][y] === 0n) continue;
            const ky = O0[x][y] ? k[x] - (O[x][y] ? 0 : 1) : k[x] + (O[y][x] ? 0 : 1);
            if (k[y] !== null) { if (k[y] !== ky) return null; }
            else { k[y] = ky; cnt++; st.push(y); }
        }
    }
    return cnt === n ? k : null;
}

/** exact z^+ and z^- in vertex coordinates (polynomials in rho): z^{+-} = X^{-T} lam_{+-}, where X is the companion of
 *  the orientation of od in vertex labels; z^{+-} spans ker(X + rho^{+-1} X^T). */
function perronVectors(od) {
    const n = od.n, UiT = transpose(invUnitri(od.U));
    return [od.lp, od.lm].map(lam => {
        const z = new Array(n);
        for (let a = 0; a < n; a++) z[od.order[a]] = od.R.reduce(lin(UiT[a], lam));
        return z;
    });
}

/** the lam sign test at od: StOk(U, +-sgn lam(e_k)), sgn lam without zeros. */
function signTest(od, lam) {
    const sg = lam.map(p => od.R.sign(p));
    return !sg.includes(0) && (stOk(od.U, sg) || stOk(od.U, sg.map(x => -x)));
}

/** certify at od in the obtuse slice chamber G with the least m >= 0 that works (Lemma gset: Certify succeeds at m iff
 *  theta rho^(2m) lies in G(sigma), whose tail lies in G(sigma) at the selected class). -> [m, C, eps] or null. */
function certifyTail(od, G, mMax) {
    if (mMax === undefined) mMax = 400;
    const Gi = intInverse(G);
    if (Gi === null) return null;
    for (let m = 0; m <= mMax; m++) {
        const C = matMul(transpose(od.power(m)), Gi); let eps = [];
        for (const r of C) {
            const any = r.some(x => x !== 0n);
            if (any && r.every(x => x >= 0n)) eps.push(1);
            else if (any && r.every(x => x <= 0n)) eps.push(-1);
            else { eps = null; break; }
        }
        if (eps === null) continue;
        if (stOk(od.U, eps)) return [m, C, eps];
        const neg = eps.map(x => -x);
        if (stOk(od.U, neg)) return [m, negMat(C), neg];
    }
    return null;
}

/** the expensive NO filters, run once a decision takes long: mutation-cyclic 4-vertex full subquivers (n >= 5) and
 *  Coxeter-polynomial candidates (n <= 5). -> reason or null. */
function lateFilters(B, f) {
    const n = B.length;
    if (n >= 5) {
        const sub = subquiverFilter(B, [4]);
        if (sub) return 'full subquiver on ' + pyList(sub[0]) + ' is not mutation-acyclic (' + sub[1] + '; [BMR])';
    }
    if (n <= 5) {
        const c = coxeterCandidates(f);
        if (c !== null && c.length === 0) return 'no connected acyclic quiver has the Coxeter polynomial of Lambda(B) (Lemma candidate)';
    }
    return null;
}

/** SELECT: one order of Lambda(B) in polynomial time, the Perron rule for the classes O^+ and O^- (Theorem 1), then
 *  descents at O^+ only. -> result, or null if inconclusive (a certificate search that should never fail, or the
 *  caps); the caller then falls back to the class search. NO answers rest on Corollary cor:Lambda, Theorem 1 (with
 *  Lemma D), (H5), Corollary R2, and R1' (classes Thm 3(ii); uses Theorem M); YES answers are certified. */
function select(B, done, stats, caps, chunk, lateAfter, progress) {
    const n = B.length, beta = maxAbs(B);
    const lam0 = windingOrder(B);
    if (lam0 === null) return done('NO', 'Lambda(B) is empty: no totally proper cyclic ordering (Theorem P, [Ne, FN])');
    const O0 = orientation(B, lam0);
    const od0 = new ExactOrder(B, linearExtension(n, O0), false);
    if (od0.type === 'none') return done('NO', 'the Coxeter matrix of Lambda(B) has no suitable real eigenvalue > 1 (H5)');
    if (od0.type === 'unit') {
        if (beta > 2n) return done('NO', 'the Coxeter polynomial of Lambda(B) is cyclotomic but some |b_ij| > 2 (finite mutation type)');
        const fs = finiteSearch(B);
        if (fs) return done('YES', 'finite mutation class with an acyclic quiver', { kind: 'mutation-path', path: fs[0], acyclic: fs[1] });
        return done('NO', 'the Coxeter polynomial of Lambda(B) is cyclotomic and the finite mutation class has no acyclic quiver');
    }
    const sel = {};
    for (const [tag, z, lamsel] of [['+', 0, od => od.lp], ['-', 1, od => od.lm]]) {
        const s = perronVectors(od0)[z].map(p => od0.R.sign(p));
        if (s.includes(0)) return done('NO', 'Perron rule ' + tag + ': z has a zero coordinate (Theorem 1)');
        const O = range(n).map(() => new Array(n).fill(false));
        for (let x = 0; x < n; x++) for (let y = 0; y < n; y++) if (O0[x][y]) { if (s[x] === s[y]) O[x][y] = true; else O[y][x] = true; }
        if (flipPotential(B, O0, O) === null) return done('NO', 'Perron rule ' + tag + ': the orientation is not in the flip class (Theorem 1)');
        const od = new ExactOrder(B, linearExtension(n, O), false);
        if (od.type !== 'wild') return null;          // impossible (flips keep the Coxeter polynomial); fall back
        if (!signTest(od, lamsel(od))) return done('NO', 'Perron rule ' + tag + ': the selected class fails its sign test (Theorem 1)');
        sel[tag] = od;
    }
    const od = sel['+'];
    let tasks = od.grid().map(s => [s, descentGen(od, s, caps, chunk)]), stuckzero = 0, lateDone = false;
    const total = tasks.length;
    while (tasks.length) {
        const nxt = [];
        for (const t of tasks) {
            const s = t[0], r = t[1].next();
            if (!r.done) { stats.steps += chunk; nxt.push(t); continue; }
            const kind = r.value[0], G = r.value[1]; stats.tasks += 1;
            if (kind === 'stuck' || kind === 'zero') {
                stuckzero += 1;
                if (stuckzero === n + 1) return done('NO', 'n+1 values of s end stuck or at a zero height at the selected order ' + pyTuple(od.order) + ' (Corollary R2)');
            } else if (kind === 'obtuse') {
                const aq = acyclicFromGamma(od.U, G);
                if (aq === null || !isConnected(aq[0]))
                    return done('NO', 'an obtuse chamber at the selected order ' + pyTuple(od.order) + " is not a connected slice chamber (R1')");
                const ce = certifyTail(od, G);
                if (ce === null) return null;                 // never happens (Lemma certexists); fall back
                const cert = packageCert(od, G, aq[0], aq[1], ce, s);
                const mp = mutationPath(B, cert); cert.path = mp[0]; cert.path_end = mp[1];
                return done('YES', 'certificate at the selected order ' + pyTuple(od.order) + ', s = ' + s.toString() + ', m = ' + ce[0], cert);
            }
        }
        tasks = nxt;
        if (progress) progress(stats.tasks, total, 'descent task', stats.steps);
        if (tasks.length && !lateDone && stats.steps >= lateAfter) {
            lateDone = true; const why = lateFilters(B, od.f);
            if (why) return done('NO', why);
        }
    }
    return null;                                      // only if every descent hit the caps
}

// test knobs of the reference test driver (rust/tests/run_py_auto.py): skip early steps (vortex, sub3, comb; also
// select, to exercise the fallback class search), run the late filters earlier; they apply to the whole top-level decide, including the nested subquiver decides (as monkeypatching does in Python)
let AUTO_SKIP = new Set(), AUTO_LATE = 4000;

/** filters, the combinatorial YES path, then SELECT (one class, polynomial selection). If SELECT is inconclusive
 *  (never observed), the Corollary 7.4 class search: one order per class of Lambda(B), interleaved descents, the n+1
 *  rejection rule, and rigorous NO filters. Always terminates; YES is certified, NO rests on Theorems D and P and, for
 *  SELECT, Theorem 1. Same reasons, certificates and scheduler stats as the reference's _decide_auto. */
function decideAuto(B, t0, progress) {
    const chunk = 32, lateAfter = AUTO_LATE;
    const n = B.length, beta = maxAbs(B);
    const stats = { select: 1, tasks: 0, steps: 0 };
    const done = (ans, why, cert) => makeResult(ans, why, cert || null, Object.assign({}, stats), t0);
    if (!AUTO_SKIP.has('vortex')) {
        const v = vortexFilter(B);
        if (v !== null) return done('NO', 'the in- or out-neighbourhood of vertex ' + v + ' has an oriented cycle ([Ne, Thm 4.4])');
    }
    if (!AUTO_SKIP.has('sub3')) {
        const sub = subquiverFilter(B, [3]);
        if (sub) return done('NO', 'full subquiver on ' + pyList(sub[0]) + ' is not mutation-acyclic (' + sub[1] + '; [BMR])');
    }
    if (!AUTO_SKIP.has('comb')) {
        const fy = combinatorialYes(B);
        if (fy) return done('YES', 'mutation sequence to an acyclic quiver (unforking + plateau search)',
                            { kind: 'mutation-path', path: fy[0], acyclic: fy[1] });
    }
    const caps = new Caps(n, beta);
    const r = AUTO_SKIP.has('select') ? null : select(B, done, stats, caps, chunk, lateAfter, progress);
    if (r !== null) return r;
    for (const k of Object.keys(stats)) delete stats[k];
    Object.assign(stats, { select: 0, classes: 0, unit: 0, none: 0, wild: 0, G_empty: 0, tasks: 0, rejected_orders: 0, steps: 0 });
    const cls = lambdaClasses(B); stats.classes = cls.length;
    if (!cls.length) return done('NO', 'Lambda(B) is empty: no totally proper cyclic ordering (Theorem P, [Ne])');
    let unit = false, tasks = [];
    const bad = new Array(cls.length).fill(0), stuckzero = new Array(cls.length).fill(0);
    cls.forEach((o, ci) => {
        const od = new ExactOrder(B, o); stats[od.type] += 1;
        if (od.type === 'unit') unit = true;
        if (od.type !== 'wild') return;
        if (!gSetNonempty(od)) { stats.G_empty += 1; return; }   // never certifies (Theorem W(a))
        for (const s of od.grid()) { tasks.push([ci, od, s, orderTask(od, s, caps, chunk)]); stats.tasks += 1; }
    });
    const total = tasks.length; let lateDone = false;
    while (tasks.length) {
        const nxt = [];
        for (const t of tasks) {
            const ci = t[0], od = t[1], s = t[2];
            if (bad[ci] > n) continue;                // order already rejected (n+1 rule)
            const r = t[3].next();
            if (!r.done) { stats.steps += chunk; nxt.push(t); continue; }
            const res = r.value[0], val = r.value[1];
            if (res === 'cert') {
                const mp = mutationPath(B, val); val.path = mp[0]; val.path_end = mp[1];
                return done('YES', 'certificate at order ' + pyTuple(od.order) + ', s = ' + s.toString(), val);
            }
            if (res === 'bad') {
                bad[ci] += 1;
                if (bad[ci] === n + 1) stats.rejected_orders += 1;
                if (val === 'stuck' || val === 'zero') {      // one-class NO rule (writeup Corollary cor:R2)
                    stuckzero[ci] += 1;
                    if (stuckzero[ci] === n + 1)
                        return done('NO', 'n+1 values of s end stuck or at a zero height at order ' + pyTuple(od.order) + ' (Corollary R2)');
                }
            }
        }
        tasks = nxt.filter(t => bad[t[0]] <= n);
        if (progress) progress(total - tasks.length, total, 'descent task', stats.steps);
        if (tasks.length && !lateDone && stats.steps >= lateAfter) {
            lateDone = true; const why = lateFilters(B, flAdjugate(coxeter(companion(B, cls[0])))[0]);
            if (why) return done('NO', why);
        }
    }
    if (unit && beta <= 2n) {
        const fs = finiteSearch(B);
        if (fs) return done('YES', 'finite mutation class with an acyclic quiver', { kind: 'mutation-path', path: fs[0], acyclic: fs[1] });
    }
    return done('NO', 'no class of Lambda(B) gives a certificate (Theorem D, Corollary 7.4)');
}

function now() { return (typeof performance !== 'undefined' && performance.now) ? performance.now() : Date.now(); }

function makeResult(answer, reason, certificate, stats, t0, comps) {
    const r = { answer: answer, reason: reason, seconds: (now() - t0) / 1000, stats: stats || {} };
    if (certificate) r.certificate = certificate;
    if (comps) r.components = comps;
    return r;
}

function decideConnected(B, orders, progress) {
    const n = B.length, t0 = now();
    if (isAcyclic(B))
        return makeResult('YES', 'the quiver is acyclic', { kind: 'acyclic-input', acyclic: copyMat(B) }, null, t0);
    if (orders === 'auto') return decideAuto(B, t0, progress);
    const beta = maxAbs(B);
    const caps = new Caps(n, beta);
    let ords, total;
    if (orders === 'all') { ords = permutations(range(n)); total = Number(factorial(n)); }
    else if (orders === 'proper') {
        ords = properRotations(B); total = ords.length;
        if (!ords.length) return makeResult('NO', 'no proper cyclic ordering (Neville)', null, { proper_orders: 0 }, t0);
    } else { ords = orders.map(o => o.slice()); total = ords.length; }
    const stats = { orders: 0, unit: 0, none: 0, wild: 0, descents: 0, obtuse: 0, stuck: 0, zero: 0, cap: 0 };
    let unit = false;
    for (const o of ords) {
        stats.orders += 1;
        if (progress) progress(stats.orders, total, 'linear order');
        const od = new ExactOrder(B, o); stats[od.type] += 1;
        if (od.type === 'unit') { unit = true; continue; }
        if (od.type !== 'wild') continue;
        for (const s of od.grid()) {
            const dg = descent(od, s, caps), kind = dg[0], G = dg[1];
            stats.descents += 1; stats[kind] += 1;
            if (kind !== 'obtuse') continue;
            const cert = walk(od, G, s);
            if (cert) {
                const mp = mutationPath(B, cert); cert.path = mp[0]; cert.path_end = mp[1];
                return makeResult('YES', 'certificate at order ' + pyTuple(od.order) + ', s = ' + s.toString(), cert, stats, t0);
            }
        }
    }
    if (unit && beta <= 2n) {
        const fs = finiteSearch(B);
        if (fs) return makeResult('YES', 'finite mutation class with an acyclic quiver',
                                  { kind: 'mutation-path', path: fs[0], acyclic: fs[1] }, stats, t0);
    }
    const why = orders === 'all' ? 'no order gives a certificate' : 'no certificate at the given orders (not a proof of NO)';
    return makeResult('NO', why, null, stats, t0);
}

let DECIDE_DEPTH = 0;

/** Decide mutation-acyclicity of the quiver B (skew-symmetric integer matrix) exactly; always 'YES' or 'NO'.
 *  opts.orders: 'auto' (default): rigorous NO filters (vortex [Ne]; mutation-cyclic full subquivers [BBH, BMR]), a
 *    combinatorial YES path, then SELECT: one order of Lambda(B) in polynomial time, the Perron rule for the single
 *    sign-passing class O^+ (writeup Theorem P, Corollary 7.4, selection theorem), and descents at O^+ only (NO by
 *    Corollary R2 or R1'); if SELECT were ever inconclusive, one order per class of Lambda(B) with interleaved descents
 *    and the n+1 rejection rule. 'all': all n! orders (guaranteed, slower). 'proper': a heuristic (NO not proved).
 *  opts.verify (default true): re-check every YES certificate independently.
 *  opts.progress(component, ncomponents, done, total, unit, steps): optional progress callback; unit is 'linear order'
 *    ('all'/'proper': called before each order) or 'descent task' ('auto': after each round of the descent scheduler,
 *    done = descent tasks finished or dropped, steps = descent steps so far).
 *  opts.autoSkip (subset of ['vortex', 'sub3', 'comb', 'select']) and opts.lateFiltersAfter (default 4000): test knobs, as
 *    MA_AUTO_SKIP / MA_AUTO_LATE of the reference test driver. */
function decide(B, opts) {
    opts = opts || {};
    const orders = opts.orders || 'auto', verify = opts.verify !== false, progress = opts.progress || null;
    if (DECIDE_DEPTH === 0) {                         // caches are shared within one top-level call only
        SPEC_CACHE.clear(); GRID_CACHE.clear();
        const sk = opts.autoSkip || [];
        AUTO_SKIP = new Set(typeof sk === 'string' ? sk.split(',') : sk);
        AUTO_LATE = opts.lateFiltersAfter !== undefined ? Number(opts.lateFiltersAfter) : 4000;
    }
    return decideBig(B, orders, verify, progress);
}

function decideBig(B, orders, verify, progress) {
    DECIDE_DEPTH++;
    try {
        B = toBigMatrix(B); checkSkew(B); const t0 = now();
        const comps = components(B);
        if (comps.length === 1) {
            const r = decideConnected(B, orders, progress ? (i, t, u, st) => progress(0, 1, i, t, u, st) : null);
            if (verify && r.answer === 'YES') {
                const v = verifyCertificate(B, r.certificate);
                if (!v[0]) throw new Error('certificate check failed: ' + v[1]);
                r.verified = v[1];
            }
            return r;
        }
        if (orders !== 'all' && orders !== 'proper' && orders !== 'auto') throw new Error('explicit orders are only supported for connected quivers');
        const results = [];
        comps.forEach((comp, ci) => {
            const Bc = submatrix(B, comp);
            const r = decideConnected(Bc, orders, progress ? (i, t, u, st) => progress(ci, comps.length, i, t, u, st) : null);
            if (verify && r.answer === 'YES') {
                const v = verifyCertificate(Bc, r.certificate);
                if (!v[0]) throw new Error('certificate check failed: ' + v[1]);
                r.verified = v[1];
            }
            results.push([comp, r]);
        });
        const ans = results.some(cr => cr[1].answer === 'NO') ? 'NO' : 'YES';
        return makeResult(ans, 'disconnected: decided componentwise', null, null, t0, results);
    } finally {
        DECIDE_DEPTH--;
    }
}

/** per component: vertices, the mutation path (component-local indices) and the acyclic quiver it reaches. */
function pathsOf(result, n) {
    const parts = result.components ? result.components : [[range(n), result]];
    return parts.map(cr => {
        const comp = cr[0], r = cr[1], c = r.certificate;
        let path = null, end = null;
        if (c) {
            if (c.kind === 'acyclic-input') { path = []; end = c.acyclic; }
            else if (c.kind === 'mutation-path') { path = c.path; end = c.acyclic; }
            else { path = c.path; end = c.path_end; }
        }
        return { vertices: comp, answer: r.answer, reason: r.reason, kind: c ? c.kind : null, path: path, end: end };
    });
}

/** deep copy with BigInts turned into decimal strings (for postMessage / JSON). */
function toPlain(x) {
    if (typeof x === 'bigint') return x.toString();
    if (Array.isArray(x)) return x.map(toPlain);
    if (x instanceof Q) return x.toString();
    if (x && typeof x === 'object') { const o = {}; for (const k in x) o[k] = toPlain(x[k]); return o; }
    return x;
}

return {
    decide: decide, verifyCertificate: verifyCertificate, pathsOf: pathsOf, toPlain: toPlain,
    mutate: mutate, isAcyclic: isAcyclic, components: components, isConnected: isConnected,
    canonical: canonical, reflectionClass: reflectionClass, fromUpper: fromUpper, upper: upper,
    toBigMatrix: toBigMatrix, checkSkew: checkSkew, uniformCaps: uniformCaps, Caps: Caps, finiteSearch: finiteSearch,
    mutationPath: mutationPath, canonicalForm: canonicalForm,
    // internals, exported for testing
    _internal: { Q: Q, qn: qn, Rho: Rho, ExactOrder: ExactOrder, flAdjugate: flAdjugate, stripCyclotomic: stripCyclotomic,
                 squarefreePart: squarefreePart, largestRootAboveOne: largestRootAboveOne, strictlyDominant: strictlyDominant,
                 descent: descent, walk: walk, certify: certify, intInverse: intInverse, fracDet: fracDet,
                 irootCeil: irootCeil, isqrt: isqrt, isRealRoot: isRealRoot, stepsAbove: stepsAbove,
                 vortexFilter: vortexFilter, subquiverFilter: subquiverFilter, combinatorialYes: combinatorialYes,
                 forkPoint: forkPoint, chordlessCycles: chordlessCycles, lambdaClasses: lambdaClasses,
                 coxeterCandidates: coxeterCandidates, gSetNonempty: gSetNonempty, chordlessCycleBasis: chordlessCycleBasis,
                 windingOrder: windingOrder, linearExtension: linearExtension, orientation: orientation,
                 flipPotential: flipPotential, perronVectors: perronVectors, certifyTail: certifyTail, detInt: detInt,
                 pySort: pySort, lateFilters: lateFilters, select: select, decideAuto: decideAuto }
};
}   // end factory

/* Web Worker entry point. Protocol:
 *   main -> worker  { cmd: 'decide', id, B: [[string]], orders? }        (orders: 'auto' (default), 'all', 'proper')
 *   worker -> main  { type: 'progress', id, component, components, order, orders, unit, steps }
 *                   { type: 'result', id, result (BigInts as strings), paths }
 *                   { type: 'error', id, message }                                                                  */
function workerMain() {
    var lastPost = 0;
    self.onmessage = function (ev) {
        var msg = ev.data || {};
        if (msg.cmd !== 'decide') return;
        try {
            var res = MutationAcyclic.decide(msg.B, {
                orders: msg.orders || 'auto',
                progress: function (ci, nc, oi, no, unit, steps) {
                    var t = Date.now();
                    if (t - lastPost > 150 || oi === no) {
                        lastPost = t;
                        self.postMessage({ type: 'progress', id: msg.id, component: ci, components: nc, order: oi, orders: no,
                                           unit: unit || 'linear order', steps: steps });
                    }
                }
            });
            self.postMessage({ type: 'result', id: msg.id, result: MutationAcyclic.toPlain(res),
                               paths: MutationAcyclic.toPlain(MutationAcyclic.pathsOf(res, msg.B.length)) });
        } catch (e) {
            self.postMessage({ type: 'error', id: msg.id, message: String(e && e.message || e) });
        }
    };
}

var api = factory();
api.workerSource = function () {
    return 'var MutationAcyclic = (' + factory.toString() + ')();\n(' + workerMain.toString() + ')();\n';
};
api._workerMain = workerMain;
if (typeof module === 'object' && module.exports) module.exports = api;
else root.MutationAcyclic = api;
})(typeof self !== 'undefined' ? self : this);
