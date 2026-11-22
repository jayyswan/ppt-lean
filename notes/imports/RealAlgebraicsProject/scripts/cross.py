"""Session 32 (step 1): continue a real S_ord line in line space while pushing u = 1/j(line) through 0
(the nodal fibre), to see whether real lines reach the two-component side (u > 0).
usage: python3 cross.py <rlines file> <index among ordinary rows> <nsteps>
Prints at each step: target u, achieved u, residual, min pair distance (Q_i +- Q_j), number of
real roots of h, and (if three) how many x_i lie on the egg."""
import numpy as np, sys, warnings; warnings.filterwarnings('ignore')
from scipy.optimize import least_squares
rows = np.load(sys.argv[1]); idx = int(sys.argv[2]); nst = int(sys.argv[3])
S = np.array([-1.3, -0.6, 0.1, 0.7, 1.4, 2.0])

def weier(Z, a):
    A = np.stack([Z, a, Z**3, Z**2*a, Z*a**2, a**3], 1)
    g = np.linalg.svd(A)[2][-1]; al, be = g[0], g[1]; nn = np.hypot(al, be)
    Zp = (al*Z + be*a)/nn; ap = (-be*Z + al*a)/nn
    B = np.stack([Zp**3, Zp**2*ap, Zp*ap**2, ap**3], 1)
    hc = -np.linalg.lstsq(B, -Zp, rcond=None)[0]
    return hc, ap/Zp
def invj(hc):
    d, c, b, A3 = hc
    p = (3*A3*c - b*b)/(3*A3*A3); q = (2*b**3 - 9*A3*b*c + 27*A3*A3*d)/(27*A3**3)
    return (4*p**3 + 27*q*q)/(1728*4*p**3)
def eqs(v):
    Z, a = v[:9], v[9:]
    out = []
    for m in (1, 3, 5):
        out += [np.sum((Z + s*a)**m) for s in S[:m+1]]
    out += [Z@Z - 1, a@a - 1, Z@a]
    return np.array(out)
def info(v):
    Z, a = v[:9], v[9:]; Q = np.stack([Z, a], 1)
    par = min(min(np.linalg.norm(Q[i]+Q[j]), np.linalg.norm(Q[i]-Q[j])) for i in range(9) for j in range(i))
    hc, x = weier(Z, a); r = np.roots(hc[::-1]); nr = int(np.sum(abs(r.imag) < 1e-9*abs(r).max()))
    kegg = -1
    if nr == 3:
        e = np.sort(r.real); hv = np.polyval(hc[::-1], x)
        # egg = bounded interval where h>0
        lead = hc[3]
        egg = (e[0], e[1]) if lead > 0 else (e[1], e[2])
        kegg = int(np.sum((x > egg[0]) & (x < egg[1])))
    return invj(hc), par, nr, kegg

ords = []
for v in rows:
    Z, a = v[:9], v[9:]
    M = np.stack([np.ones(9), Z**2, Z*a, a**2], 1); sv = np.linalg.svd(M/np.linalg.norm(M, axis=0), compute_uv=False)
    if sv[-1] > 1e-3: ords.append(v)
v = ords[idx].copy()
u0, par, nr, k = info(v)
print(f"start: u=1/j={u0:.3e} minpair={par:.2e} h real roots={nr}")
targets = np.linspace(u0, -u0*1.5, nst)
W = 1.0/abs(u0)
for t in targets[1:]:
    f = lambda w: np.r_[eqs(w), W*(info(w)[0] - t)]
    sol = least_squares(f, v, xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=400)
    res = np.abs(eqs(sol.x)).max()
    u, par, nr, k = info(sol.x)
    print(f"target {t:+.3e}  u {u:+.3e}  res {res:.1e}  minpair {par:.2e}  h-real {nr}  k_egg {k}", flush=True)
    if res > 1e-8:
        print("lost the curve"); break
    v = sol.x
np.save(f"cross_{idx}.npy", v)
