"""Real conics on L_135 = {p1=p3=p5=0} in P^8 (n=9), off the pairing spaces.
c(t) = c0 + c1 t + c2 t^2.  21 equations (3+7+11), 27 unknowns, 4-dim gauge."""
import numpy as np
from numpy.polynomial import polynomial as Pl
import sys
n = 9
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
DEG = int(sys.argv[2]) if len(sys.argv) > 2 else 2   # 1 = lines, 2 = conics

def eqs(C):  # C shape (n, DEG+1), low->high coefficients
    out, jac = [], []
    for k in (1, 3, 5):
        tot = np.zeros(k * DEG + 1)
        J = np.zeros((k * DEG + 1, n, DEG + 1))
        for i in range(n):
            pk1 = Pl.polypow(C[i], k - 1)
            pk = Pl.polymul(pk1, C[i])
            tot[:len(pk)] += pk
            for j in range(DEG + 1):
                d = k * np.concatenate([np.zeros(j), pk1])
                J[:len(d), i, j] += d
        out.append(tot); jac.append(J.reshape(len(tot), -1))
    return np.concatenate(out), np.vstack(jac)

def FJ(x):
    F, J = eqs(x.reshape(n, DEG + 1))
    return np.append(F, x @ x - 1), np.vstack([J, 2 * x])
def solve(C):
    x = C.ravel() / np.linalg.norm(C); lam = 1e-2
    F, J = FJ(x); f = F @ F
    for it in range(600):
        A = J.T @ J; g = J.T @ F
        step = np.linalg.solve(A + lam * np.eye(len(x)), g)
        xn = x - step; Fn, Jn = FJ(xn); fn = Fn @ Fn
        if fn < f:
            x, F, J, f = xn, Fn, Jn, fn; lam = max(lam / 3, 1e-12)
        else:
            lam *= 4
        if f < 1e-26 or lam > 1e8: break
    # polish with Gauss-Newton min-norm
    for it in range(20):
        x = x - np.linalg.lstsq(J, F, rcond=None)[0]; F, J = FJ(x)
    return x.reshape(n, DEG + 1), np.linalg.norm(F)

def pairing_dist(C):
    # min over pairs (i,j) of ||c_i + c_j||  and min ||c_i|| (zero coordinate)
    d = [np.linalg.norm(C[i] + C[j]) for i in range(n) for j in range(i + 1, n)]
    return min(d), min(np.linalg.norm(C, axis=1))

if __name__ == '__main__':
    found = []
    for trial in range(int(sys.argv[3]) if len(sys.argv) > 3 else 300):
        C = rng.normal(size=(n, DEG + 1))
        C, r = solve(C)
        if r > 1e-11 or not np.all(np.isfinite(C)):
            continue
        sv = np.linalg.svd(C, compute_uv=False)
        npair = sum(np.linalg.norm(C[i] + C[j]) < 1e-6 for i in range(n) for j in range(i + 1, n))
        nzero = sum(np.linalg.norm(C, axis=1) < 1e-6)
        found.append((sv[-1], npair, nzero, C))
    print('converged', len(found))
    from collections import Counter
    print('pattern (npair,nzero) counts:', Counter((f[1], f[2]) for f in found if f[0] > 1e-6))
    tag = sys.argv[1] if len(sys.argv) > 1 else '0'
    np.save(f'curves_deg{DEG}_s{tag}.npy', np.array([f[3] for f in found if f[0] > 1e-6]))
