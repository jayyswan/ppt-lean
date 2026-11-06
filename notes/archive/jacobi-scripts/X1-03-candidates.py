# X1-03: does a moving-modulus E/F combination equal am?  (fast float version)
#
# scipy.special.ellipkinc(phi,m) = incomplete F(phi,m) (parameter m)
# scipy.special.ellipeinc(phi,m) = incomplete E(phi,m)
# scipy.special.ellipj(u,m)[0]   = sn(u,m); am = arcsin(sn) for 0 < u < K.
#
# Family A (6 params): am(u,c) =? a1 E(bu,m) + a2 F(bu,m) + a3 u + a4
# Family B (4 params): am(u,c) =? a1 E(bu,m) + a2 F(bu,m)
# Fit on an interior grid; evaluate OFF-GRID.  A true identity -> ~1e-14 off-grid.
# A spurious fit -> a plateau that does not shrink.  High-precision spot re-check with
# mpmath is printed for the best fit.

import numpy as np
from scipy.optimize import least_squares
from scipy.special import ellipkinc, ellipeinc, ellipj, ellipk
import mpmath as mp

mp.mp.dps = 30


def am(u, c):
    return np.arcsin(ellipj(u, c)[0])


def make_model(small):
    if small:
        def f(th, u):
            a1, a2, b, m = th
            return a1 * ellipeinc(b * u, m) + a2 * ellipkinc(b * u, m)
        x0 = [0.0, 1.0, 1.0, 0.5]
    else:
        def f(th, u):
            a1, a2, b, m, a3, a4 = th
            return (a1 * ellipeinc(b * u, m) + a2 * ellipkinc(b * u, m)
                    + a3 * u + a4)
        x0 = [0.0, 1.0, 1.0, 0.5, 0.0, 0.0]
    return f, x0


print("c      family    train_resid   off-grid_resid            theta")
for cval in [0.09, 0.3, 0.7]:
    K = ellipk(cval)
    utr = np.linspace(0.04 * K, 0.90 * K, 12)
    ute = np.linspace(0.91 * K, 1.05 * K, 12)
    ytr, yte = am(utr, cval), am(ute, cval)
    for small in [True, False]:
        f, x0 = make_model(small)
        res = least_squares(lambda th: f(th, utr) - ytr, x0,
                            xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=5000)
        tr = np.max(np.abs(f(res.x, utr) - ytr))
        off = np.max(np.abs(f(res.x, ute) - yte))
        tag = "4-param" if small else "6-param"
        print(f"{cval:<6} {tag:8s}  {tr:.3e}     {off:.3e}   {np.round(res.x,6)}")

# high-precision spot check at one c with mpmath, using the fitted 4-param theta
print()
print("high-precision re-check (mpmath, 30 dps) of the 4-param fit at c=0.09:")
cval = 0.09
K = float(ellipk(cval))
utr = np.linspace(0.04 * K, 0.90 * K, 12)
ytr = am(utr, cval)
f, x0 = make_model(True)
res = least_squares(lambda th: f(th, utr) - ytr, x0, xtol=1e-15, ftol=1e-15)
th = [mp.mpf(str(z)) for z in res.x]
a1, a2, b, m = th


def model_mp(u):
    return (a1 * mp.quad(lambda t: mp.sqrt(1 - m * mp.sin(t) ** 2), [0, b * u])
            + a2 * mp.ellipf(b * u, m))


def am_mp(u, c):
    return mp.asin(mp.ellipfun('sn', u, c))


for u in [mp.mpf("0.5"), mp.mpf("0.9"), mp.mpf("1.2")]:
    rhs = model_mp(u)
    lhs = am_mp(u, mp.mpf(cval))
    print(f"   u={mp.nstr(u,4)}: am={mp.nstr(lhs,20)} model={mp.nstr(rhs,20)} "
          f"resid={mp.nstr(abs(lhs-rhs),5)}")
