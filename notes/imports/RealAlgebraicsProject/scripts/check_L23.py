"""Session 11: independent numerical check of Propositions L.2 and L.3 by direct optimisation on
the sphere {p1 = 0, p2 = 1} in R^9 (scipy, 600 random starts each), with no Lagrange reduction.
L.2: min g6/p2^3 = 0, attained only with seven equal coordinates. L.3: 7/60 <= p4/p2^2 <= 19/24."""
import numpy as np
from scipy.optimize import minimize
def norm(v): v = v - v.mean(); return v / np.sqrt((v**2).sum())
def pk(v, k): return (v**k).sum()
def g6(v): p2, p3, p4, p6 = pk(v,2), pk(v,3), pk(v,4), pk(v,6); return 231*p2**3 - 966*p2*p4 + 1008*p6 - 256*p3**2
rng = np.random.default_rng(7)
res = {}
for name, f in [('g6 min', lambda v: g6(norm(v))), ('p4 min', lambda v: pk(norm(v), 4)), ('p4 max', lambda v: -pk(norm(v), 4))]:
    best, arg = np.inf, None
    for _ in range(600):
        r = minimize(f, rng.normal(size=9), method='BFGS', options={'gtol': 1e-12})
        if r.fun < best: best, arg = r.fun, norm(r.x)
    res[name] = (best, np.sort(np.round(arg, 6)))
for k, (b, a) in res.items(): print(k, '%.12f' % b, a)
print('7/60 =', 7/60, ' 19/24 =', 19/24)
