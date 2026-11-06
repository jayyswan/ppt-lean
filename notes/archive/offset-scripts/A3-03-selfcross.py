"""A3-03: real self-intersections of one offset (bitangent circles).

Find (t,s), t != s, with gamma(t) + d N(t) = gamma(s) + d N(s).
Search: many random seeds for a 2x2 Newton solve; dedupe.
"""
import numpy as np
from scipy.optimize import root

def make(curve, d):
    Xc, Yc, DXc, DYc = curve
    def P(t):
        u = np.polyval(DXc[::-1], t); v = np.polyval(DYc[::-1], t)
        w = np.sqrt(u*u+v*v)
        return np.array([np.polyval(Xc[::-1], t) - d*v/w,
                         np.polyval(Yc[::-1], t) + d*u/w])
    def F(z):
        return P(z[0]) - P(z[1])
    return P, F

# cf1
Xc = np.array([7.,5.,-3.,2.]); Yc = np.array([1.,-2.,4.,1.])
DXc = np.array([5.,-6.,6.]); DYc = np.array([-2.,8.,3.])
curve = (Xc,Yc,DXc,DYc)

for d in [1.0, 2.0, 3.0, 5.0]:
    P,F = make(curve, d)
    sols = []
    rng = np.random.default_rng(0)
    for _ in range(400):
        z0 = rng.uniform(-4,4,2)
        if abs(z0[0]-z0[1]) < 0.1: continue
        r = root(F, z0, tol=1e-13)
        if not r.success: continue
        t,s = r.x
        if abs(t-s) < 1e-6: continue
        if np.linalg.norm(F(r.x)) > 1e-10: continue
        # dedupe up to swap
        if any(min(abs(t-a),abs(s-b))+min(abs(t-b),abs(s-a))<1e-7 for a,b in sols): continue
        sols.append((t,s))
    print(f"d={d}: {len(sols)} real self-intersections (t,s):")
    for t,s in sols:
        p = P(t)
        print(f"   t={t:.12f} s={s:.12f}  point=({p[0]:.12f},{p[1]:.12f})")
