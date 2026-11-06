"""B1-07: well-conditioned root-based feasibility test.

At roots r_i of q the covering condition is
     F_i := u(r_i)^2 (u'(r_i)^2 + v'(r_i)^2) - Delta v'(r_i)^2 = 0.
This avoids all polynomial-division cancellation.  We solve the 7x7 system for
u monic cubic, v' quadratic, Delta real.
"""
import numpy as np
from scipy.optimize import root
import sys


def sysfun(roots):
    roots = np.array(roots, float)

    def F(x, return_jac=False):
        a, b, c, p, qq, r, Dlt = x
        u = roots ** 3 + a * roots ** 2 + b * roots + c
        up = 3 * roots ** 2 + 2 * a * roots + b
        vp = p * roots ** 2 + qq * roots + r
        S = up ** 2 + vp ** 2
        val = u ** 2 * S - Dlt * vp ** 2
        if not return_jac:
            return val
        # Jacobian wrt a,b,c,p,qq,r,Dlt
        n = len(roots)
        J = np.empty((n, 7))
        du_da = roots ** 2; du_db = roots; du_dc = np.ones(n)
        dup_da = 2 * roots; dup_db = np.ones(n); dup_dc = np.zeros(n)
        dvp_dp = roots ** 2; dvp_dqq = roots; dvp_dr = np.ones(n)
        J[:, 0] = 2 * u * du_da * S + u ** 2 * (2 * up * dup_da)
        J[:, 1] = 2 * u * du_db * S + u ** 2 * (2 * up * dup_db)
        J[:, 2] = 2 * u * du_dc * S + u ** 2 * (2 * up * dup_dc)
        J[:, 3] = u ** 2 * (2 * vp * dvp_dp) - Dlt * 2 * vp * dvp_dp
        J[:, 4] = u ** 2 * (2 * vp * dvp_dqq) - Dlt * 2 * vp * dvp_dqq
        J[:, 5] = u ** 2 * (2 * vp * dvp_dr) - Dlt * 2 * vp * dvp_dr
        J[:, 6] = -vp ** 2
        return val, J
    return F


def solve(roots, n_starts=3000, seed=0, tol=1e-9):
    F = sysfun(roots)
    rng = np.random.default_rng(seed)
    sols = []
    for s in range(n_starts):
        x0 = rng.normal(size=7) * np.array([1., 2., 3., 1., 2., 3., 30.])
        try:
            res = root(lambda x: F(x), x0, jac=lambda x: F(x, True)[1],
                       method='hybr', options={'maxfev': 3000})
        except Exception:
            continue
        if not res.success:
            continue
        if np.max(np.abs(F(res.x))) < tol:
            xs = res.x.copy(); xs[3:6] *= -1
            if not any(np.max(np.abs(res.x - y)) < 1e-6 for y in sols):
                sols.append(res.x)
    return sols


if __name__ == '__main__':
    cases = {
        'split 1..7': list(range(1, 8)),
        'split -3..3': list(range(-3, 4)),
        'split 0..6': list(range(0, 7)),
        'symmetric ±1,±2,±3,0': [-3, -2, -1, 0, 1, 2, 3],
        'roots cos(2pi k/14)-ish': [2 * np.cos(np.pi * (2 * k + 1) / 14) for k in range(7)],
    }
    for name, rr in cases.items():
        sols = solve(rr, n_starts=1500, seed=abs(hash(name)) % 10000)
        posd = [s for s in sols if s[6] > 1e-6]
        print("%-28s  n_real=%2d  n_Delta>0=%2d  Delta range %s"
              % (name, len(sols), len(posd),
                 (round(min((s[6] for s in posd), default=0), 4),
                  round(max((s[6] for s in posd), default=0), 4))), flush=True)
