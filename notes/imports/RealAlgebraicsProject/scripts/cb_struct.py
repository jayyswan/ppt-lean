"""Structure tests on real C_b conics in L_135 (session 30).
Reads curves_deg2_s*.npy from conics135.py.  For each genuine conic (no pairing,
no zero coordinate, full rank) decide C_a / C_b by the residual line of p3 in
the plane, then test which low-degree polynomials vanish on the 9 coefficient
vectors Q_i = (c0, c1, c2) in C^3 (and on +-Q_i), compared with the generic count."""
import numpy as np, glob, itertools, sys
from collections import Counter
n = 9
files = sys.argv[1:] or sorted(glob.glob('curves_deg2_s*.npy'))
Cs = np.concatenate([np.load(f) for f in files])
rng = np.random.default_rng(0)

def good(C):
    return (not any(np.linalg.norm(C[i] + C[j]) < 1e-6 for i in range(n) for j in range(i + 1, n))
            and min(np.linalg.norm(C, axis=1)) > 1e-6
            and np.linalg.svd(C, compute_uv=False)[-1] > 0.02)

def is_Ca(C):
    pt = lambda x, y, z: C[:, 0] * x + C[:, 1] * y + C[:, 2] * z
    pts = rng.normal(size=(30, 3))
    A = np.array([[(y*y - x*z)*x, (y*y - x*z)*y, (y*y - x*z)*z] for x, y, z in pts])
    b = np.array([np.sum(pt(*q)**3) for q in pts])
    l = np.linalg.lstsq(A, b, rcond=None)[0]
    _, _, vt = np.linalg.svd(l.reshape(1, 3)); B = vt[1:]
    m0, m1 = pt(*B[0]), pt(*B[1])
    ts = np.linspace(-1, 1, 6)
    p5c = np.polyfit(ts, [np.sum((m0 + t*m1)**5) for t in ts], 5)
    sc = np.max(np.abs(np.polyfit(ts, [np.sum(np.abs(m0 + t*m1)**5) for t in ts], 5)))
    return np.max(np.abs(p5c)) / sc < 1e-10

def monos(deg):
    return [e for e in itertools.product(range(deg + 1), repeat=3) if sum(e) == deg]

def mat(Q, degs):
    cols = [np.prod(Q**np.array(e), axis=1) for d in degs for e in monos(d)]
    M = np.array(cols).T
    return M / np.linalg.norm(M, axis=0)

def rank(M, tol=1e-9):
    s = np.linalg.svd(M, compute_uv=False)
    return int(np.sum(s > tol * s[0])), s

tests = {'hom2': [2], 'hom3': [3], 'hom4': [4], 'even<=2': [0, 2], 'odd<=3': [1, 3],
         'even<=4': [0, 2, 4], 'odd<=5': [1, 3, 5], 'hom1+3': [1, 3]}
res = Counter(); good_b = []
for C in Cs:
    if not good(C): continue
    if is_Ca(C): res['C_a'] += 1; continue
    res['C_b'] += 1
    Q = C / np.linalg.norm(C)
    good_b.append(Q)
    for name, degs in tests.items():
        M = mat(Q, degs)
        r, s = rank(M)
        res[(name, M.shape[1], r)] += 1
for k, v in sorted(res.items(), key=str): print(k, v)
np.save('cb_good.npy', np.array(good_b))
