"""B1-03: auxiliary degree of the decic-line covering solution.

For the rational totally real septic q = t^7 - 7 t^5 + 14 t^3 - 7 t + 1, refine
several real solutions of W mod q = 0 to high precision and use PSLQ to find the
minimal polynomial of Delta (and of a).  A degree <= 6 over Q would make the
solution P-constructible and settle the totally real septic.
"""
import numpy as np
import sympy as sp
import mpmath as mp
from scipy.optimize import root

mp.mp.dps = 120

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)

qcoeffs = [1, 0, -7, 0, 14, 0, -7, 1]
q = sum(sp.Integer(co) * t ** (7 - i) for i, co in enumerate(qcoeffs))
u = t ** 3 + a * t ** 2 + b * t + c
up = sp.diff(u, t)
vp = p * t ** 2 + qq * t + r
W = sp.expand(u ** 2 * (up ** 2 + vp ** 2) - Dlt * vp ** 2)
_, rem = sp.div(W, q, t)
eqs = [sp.expand(rem.coeff(t, i)) for i in range(7)]

f_np = sp.lambdify(vars_, eqs, 'numpy')
J = sp.Matrix(eqs).jacobian(vars_)
f_mp_i = [sp.lambdify(vars_, eqs[i], 'mpmath') for i in range(7)]
J_mp = [[sp.lambdify(vars_, J[i, j], 'mpmath') for j in range(7)] for i in range(7)]

# find real solutions numerically
rng = np.random.default_rng(7)
sols = []
for s in range(600):
    x0 = rng.normal(size=7) * np.array([2., 4., 4., 2., 4., 4., 4.])
    res = root(lambda x: np.asarray(f_np(*x), float), x0, method='hybr',
               options={'maxfev': 4000})
    if res.success and np.max(np.abs(np.asarray(f_np(*res.x), float))) < 1e-8:
        xs = res.x.copy(); xs[3:6] *= -1
        if not any(np.max(np.abs(res.x - y)) < 1e-5 for y in sols):
            sols.append(res.x)
print("real solutions found (mod v' sign):", len(sols))


def refine(x0):
    x = [mp.mpf(v) for v in x0]
    for it in range(60):
        F = mp.matrix([f_mp_i[i](*x) for i in range(7)])
        M = mp.matrix(7, 7)
        for i in range(7):
            for j in range(7):
                M[i, j] = J_mp[i][j](*x)
        try:
            dx = mp.lu_solve(M, F)
        except Exception:
            return None
        x = [x[i] - dx[i] for i in range(7)]
        if max(abs(F[i]) for i in range(7)) < mp.mpf('1e-110'):
            break
    return x


def min_poly(val, maxdeg=30):
    """PSLQ search for integer polynomial of val, degree <= maxdeg."""
    P = mp.mpf(val)
    for d in range(1, maxdeg + 1):
        vec = [P ** k for k in range(d + 1)]
        rel = mp.pslq(vec, maxcoeff=10 ** 60, maxsteps=10000, tol=mp.mpf('1e-95'))
        if rel is not None and rel[-1] != 0:
            # verify
            s = sum(mp.mpf(co) * P ** k for k, co in enumerate(rel))
            if abs(s) < mp.mpf('1e-80'):
                return d, rel
    return None, None


results = []
for x0 in sols:
    xr = refine(x0)
    if xr is None:
        continue
    # verify exact residual
    rmax = max(abs(f_mp_i[i](*xr)) for i in range(7))
    dD, pD = min_poly(xr[6])
    da, pa = min_poly(xr[0])
    results.append((xr, rmax, dD, pD, da, pa))
    print("a=%.10f  Delta=%.10f  resid=%.1e  deg(Delta)=%s deg(a)=%s"
          % (float(xr[0]), float(xr[6]), float(rmax), dD, da), flush=True)

print("\n=== degrees of Delta over Q ===")
print(sorted(set(str(dd) for (_, _, dd, _, _, _) in results)))
print("=== degrees of a over Q ===")
print(sorted(set(str(da) for (_, _, _, _, da, _) in results)))

