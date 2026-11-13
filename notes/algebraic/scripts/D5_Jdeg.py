"""D5: Pluecker degree of the generic jump curve J'_pi in G(2, Lambda_pi) = G(2,4).
Points of J' on one sigma_1 hyperplane {l meets the fixed line PQ}: det[A; B; P; Q] = 0.
Unknowns: chart z = (a2, a3, b2, b3) (A = (1,0,a2,a3), B = (0,1,b2,b3)) and kernel s (8, normalised r.s = 1).
Keep: kernel dim 1, no proportionality pattern (the 2-dim special loci are discarded), isolated (full-rank Jacobian).
Usage: py -I D5_Jdeg.py SEED NSTARTS"""
import sys, numpy as np
from numpy.polynomial import polynomial as P
src = open('D5_jump.py').read()
exec(src[src.index('def Mmat'):src.index('# 1. generic rank')])
src3 = open('D5_jump3.py').read()
exec(src3[src3.index('def pattern'):src3.index('cnt = Counter()')].replace('AB(z)', 'ABf(z)'))
def ABf(z): return np.array([1, 0, z[0], z[1]]), np.array([0, 1, z[2], z[3]])
rng = np.random.default_rng(int(sys.argv[1])); nst = int(sys.argv[2])
hr = np.random.default_rng(99)
Pp = hr.normal(size=4) + 1j * hr.normal(size=4); Qq = hr.normal(size=4) + 1j * hr.normal(size=4)
r = hr.normal(size=8) + 1j * hr.normal(size=8)
def G(w):
    A, B = ABf(w[:4])
    return np.concatenate([Mmat(A, B) @ w[4:], [r @ w[4:] - 1, np.linalg.det(np.array([A, B, Pp, Qq]))]])
def nj(f, w, h=1e-7):
    f0 = f(w); J = np.zeros((len(f0), len(w)), complex)
    for k in range(len(w)):
        e = np.zeros(len(w), complex); e[k] = h; J[:, k] = (f(w + e) - f0) / h
    return J
sols = []
for _ in range(nst):
    w = rng.normal(size=12) + 1j * rng.normal(size=12)
    ok = False
    for it in range(80):
        g = G(w)
        if np.linalg.norm(g) < 1e-13: ok = True; break
        try: w = w + np.linalg.solve(nj(G, w), -g)
        except np.linalg.LinAlgError: break
        if np.linalg.norm(w) > 1e4: break
    if not ok: continue
    A, B = ABf(w[:4])
    sv = np.linalg.svd(Mmat(A, B), compute_uv=False)
    if sv[-2] < 1e-8 * sv[0] or pattern(w[:4]): continue
    if np.linalg.svd(nj(G, w), compute_uv=False)[-1] < 1e-9: continue
    if all(np.linalg.norm(w[:4] - v) > 1e-6 * (1 + np.linalg.norm(v)) for v in sols): sols.append(w[:4])
print(f"seed {sys.argv[1]} starts {nst}: distinct isolated points of J' on sigma_1: {len(sols)}")
np.save(f"Jdeg_seed{sys.argv[1]}.npy", np.array(sols))
