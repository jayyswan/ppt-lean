"""Session 27 copy of linepairs.py (session 26) with a __main__ guard so it can be imported.
Unknowns Z, a, b in R^9: lines Z + s a, Z + t b.  Equations: p_k(Z + s a) = 0 identically in s
(k = 1, 3, 5), same for b (the s^0 terms are shared): 3 + 9 + 9 = 21, plus normalisation
|Z| = 1, <Z,a> = <Z,b> = 0, |a| = |b| = 1 (5).  27 unknowns, 26 equations: expected 1-dim family.
usage: python3 linepairs.py seed starts   -> writes pairs_<seed>.npy"""
import numpy as np, sys
from math import comb
n = 9

def line_eqs(Z, a, with0):
    out, J = [], []
    for k in (1, 3, 5):
        for j in range(0 if with0 else 1, k + 1):
            c = comb(k, j)
            out.append(c * np.sum(Z**(k - j) * a**j))
            dZ = c * (k - j) * Z**max(k - j - 1, 0) * a**j if k - j > 0 else np.zeros(n)
            da = c * j * Z**(k - j) * a**max(j - 1, 0) if j > 0 else np.zeros(n)
            J.append((dZ, da))
    return out, J

def FJ(x):
    Z, a, b = x[:9], x[9:18], x[18:]
    F, rows = [], []
    o, J = line_eqs(Z, a, True)
    for v, (dZ, da) in zip(o, J):
        F.append(v); rows.append(np.concatenate([dZ, da, np.zeros(9)]))
    o, J = line_eqs(Z, b, False)
    for v, (dZ, db) in zip(o, J):
        F.append(v); rows.append(np.concatenate([dZ, np.zeros(9), db]))
    F += [Z @ Z - 1, Z @ a, Z @ b, a @ a - 1, b @ b - 1]
    rows += [np.concatenate([2 * Z, 0 * Z, 0 * Z]), np.concatenate([a, Z, 0 * Z]),
             np.concatenate([b, 0 * Z, Z]), np.concatenate([0 * Z, 2 * a, 0 * Z]),
             np.concatenate([0 * Z, 0 * Z, 2 * b])]
    return np.array(F), np.array(rows)

def solve(x):
    lam = 1e-2; F, J = FJ(x); f = F @ F
    for it in range(800):
        step = np.linalg.solve(J.T @ J + lam * np.eye(len(x)), J.T @ F)
        xn = x - step; Fn, Jn = FJ(xn); fn = Fn @ Fn
        if fn < f: x, F, J, f = xn, Fn, Jn, fn; lam = max(lam / 3, 1e-12)
        else: lam *= 4
        if f < 1e-28 or lam > 1e9: break
    for it in range(15):
        x = x - np.linalg.lstsq(J, F, rcond=None)[0]; F, J = FJ(x)
    return x, np.linalg.norm(F), J

def degenerate(Z, a, b):
    for v in (a, b):
        M = np.stack([Z, v], 1)
        if min(np.linalg.norm(M, axis=1)) < 1e-5: return 'zero'
        if min(np.linalg.norm(M[i] + M[j]) for i in range(n) for j in range(i + 1, n)) < 1e-5: return 'pair'
    if np.linalg.svd(np.stack([Z, a, b], 1), compute_uv=False)[-1] < 1e-5: return 'collinear'
    return None

if __name__ == '__main__':
    seed = int(sys.argv[1]); starts = int(sys.argv[2])
    rng = np.random.default_rng(seed)
    good, stats = [], {}
    for s in range(starts):
        x, r, J = solve(rng.normal(size=27))
        if r > 1e-11: stats['fail'] = stats.get('fail', 0) + 1; continue
        d = degenerate(x[:9], x[9:18], x[18:])
        if d: stats[d] = stats.get(d, 0) + 1; continue
        rk = np.linalg.matrix_rank(J, 1e-8)
        stats[('ok', rk)] = stats.get(('ok', rk), 0) + 1
        good.append(x)
    print(stats)
    np.save('pairs_%d.npy' % seed, np.array(good))
