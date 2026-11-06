"""B1-14: calibration of the decic engine on a TOTALLY REAL OCTIC over Q.

The decic family has 7 effective unknowns; covering a degree-8 q needs 8 equations
(W mod q = 0 has 8 coefficients), so the count says the system is overdetermined by 1
and generically unsolvable.  The octic root is nevertheless in K by
root_Pconstructible_le_eight.  This script checks the overdetermined count numerically:
min residual over random least-squares starts should stay bounded away from 0.
Also runs a septics sanity check (should be solvable).
"""
import numpy as np
from scipy.optimize import least_squares


def F(x, roots):
    a, b, c, p, qq, r, Dlt = x
    return np.array([
        (ri**3 + a * ri**2 + b * ri + c)**2
        * ((3 * ri**2 + 2 * a * ri + b)**2 + (p * ri**2 + qq * ri + r)**2)
        - Dlt * (p * ri**2 + qq * ri + r)**2
        for ri in roots])


def scan(roots, nstarts=400, seed=0, label=""):
    rng = np.random.default_rng(seed)
    best = np.inf
    good = 0
    for _ in range(nstarts):
        x0 = rng.normal(size=7) * np.array([1., 2., 3., 1., 2., 3., 50.])
        try:
            res = least_squares(lambda x: F(x, roots), x0, xtol=1e-14, ftol=1e-14)
        except Exception:
            continue
        m = float(np.max(np.abs(F(res.x, roots))))
        best = min(best, m)
        if m < 1e-8 and res.x[6] > 1e-6:
            good += 1
    print("%-22s nroots=%d  best|resid|=%.3e  solutions with Delta>0: %d/%d"
          % (label, len(roots), best, good, nstarts), flush=True)
    return best, good


def totally_real_octic(seed=5):
    rng = np.random.default_rng(seed)
    base = np.array([2 * np.cos(np.pi * (2 * k + 1) / 16) for k in range(8)])  # T8 roots
    for _ in range(20000):
        roots = base + rng.normal(scale=0.05, size=8)
        qc = np.poly(roots)  # monic, high->low
        if np.max(np.abs(np.roots(qc).imag)) < 1e-8:
            return np.sort(roots), qc
    raise RuntimeError


def totally_real_septic(seed=5):
    rng = np.random.default_rng(seed + 1)
    base = np.array([2 * np.cos(np.pi * (2 * k + 1) / 14) for k in range(7)])
    for _ in range(20000):
        roots = base + rng.normal(scale=0.05, size=7)
        qc = np.poly(roots)
        if np.max(np.abs(np.roots(qc).imag)) < 1e-8:
            return np.sort(roots), qc
    raise RuntimeError


if __name__ == '__main__':
    ro, qo = totally_real_octic()
    print("octic q (high->low):", np.round(qo, 4), " all real:", np.max(np.abs(np.roots(qo).imag)) < 1e-8)
    scan(ro, 400, 21, "octic (overdetermined)")
    rs, qs = totally_real_septic()
    print("septic q (high->low):", np.round(qs, 4))
    scan(rs, 400, 22, "septic (square)")
