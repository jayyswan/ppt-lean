# v3dec71.py -- session 71: real points of V_3 = {Tr u = Tr u^2 = Tr u^3 = 0} in degree 10
# (Tschirnhaus variety of x^10 = sextic: power law x^10 x Q-sextic graph, over Q).
# For each signature r (r + 2s = 10) run N Newton starts in R^r x C^s; report how many converge to a
# point with Jacobian rank 3 and pairwise distinct coordinates (a generator), and its charpoly shape.
# usage: python3 v3dec71.py [N=40] [seed=1]
import sys
import numpy as np
N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = np.random.default_rng(seed)

def coords(v, r, s):
    re = v[:r]; z = v[r:r + s] + 1j * v[r + s:]
    return np.concatenate([re, z, np.conj(z)])

def F(v, r, s):
    y = coords(v, r, s)
    return np.array([np.sum(y**k).real for k in (1, 2, 3)])

def J(v, r, s, h=1e-7):
    f0 = F(v, r, s); cols = []
    for i in range(len(v)):
        e = np.zeros(len(v)); e[i] = h
        cols.append((F(v + e, r, s) - f0) / h)
    return np.array(cols).T

for r in range(0, 11, 2):
    s = (10 - r) // 2
    good = 0; shape = None
    for _ in range(N):
        v = rng.normal(size=r + 2 * s)
        v /= np.linalg.norm(v)
        ok = False
        for it in range(60):
            f = F(v, r, s)
            if np.linalg.norm(f) < 1e-13:
                ok = True; break
            Jm = J(v, r, s)
            v = v - np.linalg.lstsq(Jm, f, rcond=None)[0]
            v /= np.linalg.norm(v)
        if not ok:
            continue
        y = coords(v, r, s)
        sep = min(abs(y[i] - y[j]) for i in range(10) for j in range(i + 1, 10))
        rk = np.linalg.matrix_rank(J(v, r, s), tol=1e-5)
        if sep > 1e-4 and rk == 3:
            good += 1
            ch = np.poly(y).real
            shape = [10 - k for k, a in enumerate(ch) if abs(a) > 1e-9]
    print('r = %2d, s = %d: %d of %d starts give smooth generators; charpoly degrees %s' % (r, s, good, N, shape))
