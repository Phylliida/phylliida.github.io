/*
 * mutationAcyclic.js -- decide whether a quiver is mutation-acyclic, with exact arithmetic and guaranteed termination.
 *
 * A line-by-line port of quiver-mutation/mutation_acyclic.py (the bounded axis walk of the accompanying write-up,
 * Section 6, Algorithm 4' and the implemented variant). Every number in the decision logic is a BigInt or a rational
 * built from BigInts; there is no floating point. Real algebraic numbers rho are integer polynomials with a dyadic
 * isolating interval; signs are decided by interval evaluation with an exact zero test (gcd with the defining
 * polynomial).
 *
 *   YES answers carry a certificate re-checked by verifyCertificate(): c-vectors satisfying the Speyer-Thomas
 *   conditions (arXiv:1203.0277, Thms 1.4 and 7.2) or an explicit mutation sequence in finite type. Every YES also
 *   carries an explicit mutation sequence from the input to an acyclic quiver.
 *   NO answers rest on Theorem D of the write-up.
 *
 * The order of every computation that refines the isolating interval of rho is the same as in the Python reference,
 * so the two implementations follow identical paths and produce identical certificates.
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

/** data for one linear order sigma: companion U, Coxeter matrix c, and, if c has a strictly dominant real
 *  eigenvalue rho > 1 (type 'wild'), the eigen-functionals lam_+, lam_- and eigenvectors y_+, y_- as integer
 *  polynomials in rho. Other types: 'unit' (cyclotomic characteristic polynomial) and 'none'. */
class ExactOrder {
    constructor(B, order) {
        this.order = order.slice(); const n = B.length; this.n = n;
        this.U = companion(B, order); this.c = coxeter(this.U); this.ci = coxeterInverse(this.U);
        const fl = flAdjugate(this.c), f = fl[0], Bs = fl[1]; this.f = f;
        this._pow = new Map([[0, identity(n)]]); this._gel = new Map();
        const g = stripCyclotomic(f);
        if (g.length <= 1) { this.type = 'unit'; return; }
        const h = squarefreePart(g), iv = largestRootAboveOne(h);
        if (iv === null) { this.type = 'none'; return; }
        const R = new Rho(h, iv[0], iv[1]); this.R = R;
        if (!strictlyDominant(f, R)) { this.type = 'none'; return; }
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

    /** 2n+1 rational values s_j with s_j^(8(2n+1)) in [rho^(8j-1), rho^(8j+1)], j = 0..2n. */
    grid() {
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
function descent(od, s, Ncap, Ecap) {
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
    while (steps < Ncap) {
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
        if (mv > Ecap) return ['cap', G];
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

/** a mutation sequence taking B to an acyclic quiver, recovered from a c-vector certificate (best-first search on
 *  sum |C_ij| over the extended exchange matrix [B; C]). -> [path, acyclic quiver reached]. */
function mutationPath(B, cert) {
    const n = B.length, sigma = cert.order, V = cert.c_vectors, C = zeros(n);
    for (let a = 0; a < n; a++) for (let i = 0; i < n; i++) C[i][sigma[a]] = V[a][i];
    const key = (X, Y) => X.map(r => r.join(',')).join(';') + '|' + Y.map(r => r.join(',')).join(';');
    const norm = Y => { let s = 0n; for (const r of Y) for (const x of r) s += babs(x); return s; };
    const heap = [{ f: norm(C), d: 0, c: 0, B: B, C: C, path: [] }], seen = new Set([key(B, C)]); let cnt = 0;
    while (heap.length) {
        const e = heapPop(heap);
        if (isAcyclic(e.B)) return [e.path, e.B];
        for (let k = 0; k < n; k++) {
            const bc = extendedMutate(e.B, e.C, k), kk = key(bc[0], bc[1]);
            if (seen.has(kk)) continue;
            seen.add(kk); cnt += 1;
            heapPush(heap, { f: norm(bc[1]), d: e.d + 1, c: cnt, B: bc[0], C: bc[1], path: e.path.concat([k]) });
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

/** breadth-first search over the quivers with all |b_ij| <= 2 that are mutation equivalent to B through such
 *  quivers (a finite set). -> [path, acyclic quiver] or null. Complete for finite mutation type (FST). */
function finiteSearch(B) {
    const n = B.length;
    const key = n <= 6 ? (X => canonical(X).join(',')) : (X => X.map(r => r.join(',')).join(';'));
    const seen = new Set([key(B)]), dq = [[B, []]]; let head = 0;
    while (head < dq.length) {
        const X = dq[head][0], path = dq[head][1]; head++;
        if (isAcyclic(X)) return [path, X];
        for (let k = 0; k < n; k++) {
            const Y = mutate(X, k);
            let big = false;
            for (const r of Y) { for (const x of r) if (babs(x) > 2n) { big = true; break; } if (big) break; }
            if (big) continue;
            const ky = key(Y);
            if (!seen.has(ky)) { seen.add(ky); dq.push([Y, path.concat([k])]); }
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
    let beta = 0n;
    for (const r of B) for (const x of r) if (babs(x) > beta) beta = babs(x);
    const caps = uniformCaps(n, beta), Ncap = caps[0], Ecap = caps[1];
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
        if (progress) progress(stats.orders, total);
        const od = new ExactOrder(B, o); stats[od.type] += 1;
        if (od.type === 'unit') { unit = true; continue; }
        if (od.type !== 'wild') continue;
        for (const s of od.grid()) {
            const dg = descent(od, s, Ncap, Ecap), kind = dg[0], G = dg[1];
            stats.descents += 1; stats[kind] += 1;
            if (kind !== 'obtuse') continue;
            const cert = walk(od, G, s);
            if (cert) {
                const mp = mutationPath(B, cert); cert.path = mp[0]; cert.path_end = mp[1];
                return makeResult('YES', 'certificate at order (' + od.order.join(', ') + (n === 1 ? ',' : '') + '), s = ' + s.toString(),
                                  cert, stats, t0);
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

/** Decide mutation-acyclicity of the quiver B (skew-symmetric integer matrix) exactly; always 'YES' or 'NO'.
 *  opts.orders: 'all' (default, the guaranteed decision) or 'proper' (NO answers rely on Conjecture P).
 *  opts.verify (default true): re-check every YES certificate independently.
 *  opts.progress(component, ncomponents, orderIndex, nOrders): optional progress callback. */
function decide(B, opts) {
    opts = opts || {};
    const orders = opts.orders || 'all', verify = opts.verify !== false, progress = opts.progress;
    B = toBigMatrix(B); checkSkew(B); const t0 = now();
    const comps = components(B);
    if (comps.length === 1) {
        const r = decideConnected(B, orders, progress ? (i, t) => progress(0, 1, i, t) : null);
        if (verify && r.answer === 'YES') {
            const v = verifyCertificate(B, r.certificate);
            if (!v[0]) throw new Error('certificate check failed: ' + v[1]);
            r.verified = v[1];
        }
        return r;
    }
    if (orders !== 'all' && orders !== 'proper') throw new Error('explicit orders are only supported for connected quivers');
    const results = [];
    comps.forEach((comp, ci) => {
        const Bc = comp.map(i => comp.map(j => B[i][j]));
        const r = decideConnected(Bc, orders, progress ? (i, t) => progress(ci, comps.length, i, t) : null);
        if (verify && r.answer === 'YES') {
            const v = verifyCertificate(Bc, r.certificate);
            if (!v[0]) throw new Error('certificate check failed: ' + v[1]);
            r.verified = v[1];
        }
        results.push([comp, r]);
    });
    const ans = results.some(cr => cr[1].answer === 'NO') ? 'NO' : 'YES';
    return makeResult(ans, 'disconnected: decided componentwise', null, null, t0, results);
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
    toBigMatrix: toBigMatrix, checkSkew: checkSkew, uniformCaps: uniformCaps, finiteSearch: finiteSearch,
    mutationPath: mutationPath,
    // internals, exported for testing
    _internal: { Q: Q, qn: qn, Rho: Rho, ExactOrder: ExactOrder, flAdjugate: flAdjugate, stripCyclotomic: stripCyclotomic,
                 squarefreePart: squarefreePart, largestRootAboveOne: largestRootAboveOne, strictlyDominant: strictlyDominant,
                 descent: descent, walk: walk, certify: certify, intInverse: intInverse, fracDet: fracDet,
                 irootCeil: irootCeil, isqrt: isqrt, isRealRoot: isRealRoot, stepsAbove: stepsAbove }
};
}   // end factory

/* Web Worker entry point. Protocol:
 *   main -> worker  { cmd: 'decide', id, B: [[string]], orders? }
 *   worker -> main  { type: 'progress', id, component, components, order, orders }
 *                   { type: 'result', id, result (BigInts as strings), paths }
 *                   { type: 'error', id, message }                                                                  */
function workerMain() {
    var lastPost = 0;
    self.onmessage = function (ev) {
        var msg = ev.data || {};
        if (msg.cmd !== 'decide') return;
        try {
            var res = MutationAcyclic.decide(msg.B, {
                orders: msg.orders || 'all',
                progress: function (ci, nc, oi, no) {
                    var t = Date.now();
                    if (t - lastPost > 150 || oi === no) {
                        lastPost = t;
                        self.postMessage({ type: 'progress', id: msg.id, component: ci, components: nc, order: oi, orders: no });
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
