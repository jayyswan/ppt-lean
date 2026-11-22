# census71.py -- session 71: power curve y^q = x^p (any P-affine image) x cubic Bezier (X(t), Y(t)).
# After pulling the affine map back onto the Bezier, the crossing polynomial is N = Y^q - X^p.
# The cusp (0,0) of the power curve is a P-rational point; a Bezier through it absorbs crossings.
# Patterns: degrees (dx, dy) of X, Y (<= 3); passages through the cusp: none, at t = 0 with
# vanishing orders (a, b), or at t = 0 and t = 1 (a node of the Bezier at the cusp), orders (1,1) each.
# For every pattern with stripped degree n in {9, 10}: number of dials, rank of the family of monic
# polynomials (dim), with translations t -> t + c added (dimT = dim of the Tschirnhaus variety in K),
# and the real-root counts reached by random real members (histogram).
# usage: python3 census71.py [nsamples=4000] [pmax=12] [seed=1]
import sys, itertools, math
import numpy as np
from numpy.polynomial import polynomial as Pl

ns = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
pmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = np.random.default_rng(seed)

def ppow(c, k):
    r = np.array([1.0 + 0j])
    for _ in range(k):
        r = Pl.polymul(r, c)
    return r

def build(pattern, dials):
    # returns X, Y coefficient arrays (low->high) from dial vector
    (dx, dy, kind, a, b) = pattern
    if kind == 'none':
        nX, nY = dx + 1, dy + 1
        X = dials[:nX]; Y = dials[nX:nX + nY]
        return np.array(X), np.array(Y)
    if kind == 'one':
        nX, nY = dx - a + 1, dy - b + 1
        X = np.concatenate([np.zeros(a), dials[:nX]]); Y = np.concatenate([np.zeros(b), dials[nX:nX + nY]])
        return X, Y
    if kind == 'two':   # X = t(t-1) X'', Y = t(t-1) Y''
        nX, nY = dx - 1, dy - 1
        base = np.array([0, -1, 1.0])
        X = Pl.polymul(base, dials[:nX]); Y = Pl.polymul(base, dials[nX:nX + nY])
        return X, Y

def ndials(pattern):
    (dx, dy, kind, a, b) = pattern
    if kind == 'none': return dx + dy + 2
    if kind == 'one': return dx - a + 1 + dy - b + 1
    return dx - 1 + dy - 1

def strip(N, kind, tol=1e-9):
    # remove factors t^k (and (t-1)^k for 'two'); return stripped poly, removed multiplicities
    N = np.trim_zeros(N, 'b')
    k0 = 0
    while len(N) > 1 and abs(N[0]) < tol * np.max(np.abs(N)):
        N = N[1:]; k0 += 1
    k1 = 0
    if kind == 'two':
        while True:
            qt, rm = Pl.polydiv(N, np.array([-1, 1.0]))
            if abs(Pl.polyval(1.0, N)) < tol * np.max(np.abs(N)) and len(N) > 1:
                N = qt; k1 += 1
            else:
                break
    return N, k0, k1

def family_dims(p, q, pattern, trials=2):
    best = (0, 0, 0, (0, 0))
    nd = ndials(pattern)
    for _ in range(trials):
        dv = rng.normal(size=nd) + 1j * rng.normal(size=nd)
        X, Y = build(pattern, dv)
        N = Pl.polysub(ppow(Y, q), ppow(X, p))
        Ns, k0, k1 = strip(N, pattern[2])
        n = len(Ns) - 1
        cols = []
        h = 1e-6
        for j in range(nd):
            e = np.zeros(nd, complex); e[j] = h
            X2, Y2 = build(pattern, dv + e)
            N2 = Pl.polysub(ppow(Y2, q), ppow(X2, p))
            # divide by the same stripped factor
            fac = np.array([1.0 + 0j])
            for _ in range(k0): fac = Pl.polymul(fac, [0, 1])
            for _ in range(k1): fac = Pl.polymul(fac, [-1, 1])
            qt, rm = Pl.polydiv(N2, fac)
            v = np.zeros(n + 1, complex); m = min(n + 1, len(qt)); v[:m] = qt[:m]
            cols.append((v - Ns) / h)
        A = np.array(cols + [Ns])
        sv = np.linalg.svd(A, compute_uv=False)
        rk = int(np.sum(sv > 1e-6 * sv[0]))
        dNs = Pl.polyder(Ns); vT = np.zeros(n + 1, complex); vT[:len(dNs)] = dNs
        AT = np.vstack([A, vT])
        svT = np.linalg.svd(AT, compute_uv=False)
        rkT = int(np.sum(svT > 1e-6 * svT[0]))
        best = max(best, (n, rk - 1, rkT - 1, (k0, k1)))
    return best

def real_counts(p, q, pattern, n):
    nd = ndials(pattern)
    hist = {}
    for _ in range(ns):
        sc = np.exp(rng.normal(size=nd) * 1.0)
        dv = rng.normal(size=nd) * sc
        X, Y = build(pattern, dv.astype(complex))
        N = Pl.polysub(ppow(Y, q), ppow(X, p)).real
        Ns, k0, k1 = strip(N.astype(complex), pattern[2], tol=1e-12)
        Ns = Ns.real
        if len(Ns) - 1 != n:
            continue
        rts = np.roots(Ns[::-1])
        nr = int(np.sum(np.abs(rts.imag) < 1e-7 * (1 + np.abs(rts.real))))
        hist[nr] = hist.get(nr, 0) + 1
    return dict(sorted(hist.items()))

pats = []
for dx in (1, 2, 3):
    for dy in (1, 2, 3):
        pats.append((dx, dy, 'none', 0, 0))
        for a in range(1, dx + 1):
            for b in range(1, dy + 1):
                pats.append((dx, dy, 'one', a, b))
        if dx >= 2 and dy >= 2:
            pats.append((dx, dy, 'two', 1, 1))

rows = []
for p in range(1, pmax + 1):
    for q in range(1, pmax + 1):
        if math.gcd(p, q) != 1 or p <= q:   # y^q = x^p with p > q; x/y swap covers the rest
            continue
        for pat in pats:
            # skip patterns where X or Y vanishes identically
            n, dim, dimT, ks = family_dims(p, q, pat)
            if n not in (9, 10):
                continue
            rows.append((n, p, q, pat, ndials(pat), dim, dimT, ks))

rows.sort(key=lambda r: (r[0], -r[6], r[1], r[2]))
print('n  p/q  (dx,dy,kind,a,b)   dials  dim  dimT  codimT  removed(t^k0,(t-1)^k1)  real-root counts')
for (n, p, q, pat, nd, dim, dimT, ks) in rows:
    hist = real_counts(p, q, pat, n)
    print(n, '%d/%d' % (p, q), pat, nd, dim, dimT, n - dimT, ks, hist, flush=True)
