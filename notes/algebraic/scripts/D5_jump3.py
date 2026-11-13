"""D5: jump locus J of the normal map on G(2, Lambda_pi), with clean local dimensions.
At a point z0 with right kernel s (dim kd) and left kernel U (dim 10 - 8 + kd), J is locally
{z : U^T M(z) S = 0} to first order, so dim_z0 J <= 4 - rank d(U^T M S)/dz. For kd = 1 this is exact
(determinantal locus, smooth point iff that rank is 3)."""
import sys, numpy as np
from collections import Counter
from numpy.polynomial import polynomial as P
src = open('D5_jump.py').read()
exec(src[src.index('def Mmat'):src.index('# 1. generic rank')])
rng = np.random.default_rng(int(sys.argv[1])); nst = int(sys.argv[2])
def AB(z): return np.array([1, 0, z[0], z[1]]), np.array([0, 1, z[2], z[3]])
def Mz(z): return Mmat(*AB(z))
r = rng.normal(size=8) + 1j * rng.normal(size=8)
def G(w):
    return np.concatenate([Mz(w[:4]) @ w[4:], [r @ w[4:] - 1]])
def nj(f, w, h=1e-7):
    f0 = f(w); J = np.zeros((len(f0), len(w)), complex)
    for k in range(len(w)):
        e = np.zeros(len(w), complex); e[k] = h; J[:, k] = (f(w + e) - f0) / h
    return J
def solve(w):
    for _ in range(200):
        g = G(w)
        if np.linalg.norm(g) < 1e-13: return w
        w = w + np.linalg.lstsq(nj(G, w), -g, rcond=None)[0]
        if np.linalg.norm(w) > 1e4: return None
    return w if np.linalg.norm(G(w)) < 1e-11 else None
def pattern(z):
    A, B = AB(z); al = [np.array([A[i], B[i]]) for i in range(4)]; pat = []
    for i in range(4):
        if np.linalg.norm(al[i]) < 1e-6: pat.append(f"a{i}=0")
    for i in range(4):
        for j in range(i):
            if min(np.linalg.norm(al[i]), np.linalg.norm(al[j])) > 1e-6 and abs(al[i][0]*al[j][1]-al[i][1]*al[j][0]) < 1e-6:
                lam = (al[i] @ al[j].conj()) / (al[j] @ al[j].conj())
                tag = "+-1" if min(abs(lam-1), abs(lam+1)) < 1e-6 else ("+-i" if min(abs(lam-1j), abs(lam+1j)) < 1e-6 else f"{lam:.3f}")
                pat.append(f"a{i}~a{j}({tag})")
    return tuple(pat)
cnt = Counter(); examples = {}; allpts = {}
for _ in range(nst):
    w = solve(rng.normal(size=12) + 1j * rng.normal(size=12))
    if w is None: continue
    z = w[:4]; M = Mz(z)
    Uf, sv, Vh = np.linalg.svd(M)
    kd = int(np.sum(sv < 1e-8 * sv[0])) + (8 - len(sv))
    S = Vh.conj().T[:, 8 - kd:]                      # right kernel basis 8 x kd
    U = Uf[:, 8 - kd:]                               # left kernel basis 10 x (2 + kd)
    def phi(zz): return (U.conj().T @ Mz(zz) @ S).ravel()
    Jp = nj(phi, z)
    dimJ = 4 - np.linalg.matrix_rank(Jp, tol=1e-5)
    key = (kd, dimJ, tuple(x if '(' not in x or '+-' in x else x.split('(')[0] + '(other)' for x in pattern(z)))
    cnt[key] += 1; examples.setdefault(key, (z, pattern(z))); allpts.setdefault(key, []).append(z)
for key, v in sorted(cnt.items(), key=lambda kv: -kv[1]):
    print(v, "kernel dim", key[0], "local dim of J <=", key[1], "pattern", key[2], "e.g.", examples[key][1])
import pickle
pickle.dump(allpts, open('jump_points.pkl', 'wb'))
