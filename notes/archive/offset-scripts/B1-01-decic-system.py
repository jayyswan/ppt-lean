"""B1-01: the reduced covering system for the decic line (offset-cubic x line) family.

We ask: does there exist a monic cubic u = t^3 + a t^2 + b t + c, a quadratic
v' = p t^2 + q t + r, and a real Delta = D^2 >= 0, such that

    W(t) := u(t)^2 * (u'(t)^2 + v'(t)^2) - Delta * v'(t)^2

is divisible by a given monic septic q?  (Then W = q*g with g cubic, and every
real root of q is a root of W, hence P-constructible by
offsetCubicPairCross_root_Pconstructible, choosing the sign of d.)

Divisibility <=> W mod q = 0, a vector equation with 7 scalar equations in the
7 unknowns a,b,c,p,q,r,Delta.  Equivalently the two vectors
    R1 = (u^2 (u'^2+v'^2)) mod q ,  R2 = (v'^2) mod q
are proportional with ratio Delta.

This script builds the exact system, and (optionally) numerically solves it for
random totally real septics.
"""
import sys
import numpy as np
import sympy as sp

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)


def make_system(qcoeffs):
    """qcoeffs: monic septic coefficients high->low, len 8 (leading 1)."""
    q = sum(sp.Integer(int(co)) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    u = t ** 3 + a * t ** 2 + b * t + c
    up = sp.diff(u, t)
    vp = p * t ** 2 + qq * t + r
    R1 = sp.expand(u ** 2 * (up ** 2 + vp ** 2))
    R2 = sp.expand(vp ** 2)
    W = sp.expand(R1 - Dlt * R2)
    _, rem = sp.div(W, q, t)
    rem = sp.expand(rem)
    eqs = [sp.expand(rem.coeff(t, i)) for i in range(7)]
    return q, eqs, R1, R2


def real_roots(qcoeffs):
    rr = np.roots(qcoeffs)
    return rr


def solve_numeric(eqs, n_starts=2000, seed=0):
    rng = np.random.default_rng(seed)
    f = sp.lambdify(vars_, eqs, 'numpy')

    def F(x):
        out = np.array(f(*x), dtype=float)
        return out

    sols = []
    for s in range(n_starts):
        # scale-staggered random start
        x0 = rng.normal(size=7) * np.array([2.0, 4.0, 4.0, 2.0, 4.0, 4.0, 4.0])
        try:
            from scipy.optimize import root
            res = root(F, x0, method='hybr', options={'maxfev': 4000})
        except Exception:
            continue
        if not res.success:
            continue
        val = np.max(np.abs(F(res.x)))
        if val < 1e-8:
            sols.append((res.x.copy(), val))
    # dedupe
    uniq = []
    for x, val in sols:
        if not any(np.max(np.abs(x - y)) < 1e-5 for y, _ in uniq):
            uniq.append((x, val))
    return uniq


def main():
    # Chebyshev-based totally real septic: t^7 - 7 t^5 + 14 t^3 - 7 t + eps
    base = [1, 0, -7, 0, 14, 0, -7, 0]
    eps = 1  # integer perturbation preserving 7 real roots hopefully
    qc = base.copy()
    qc[7] = eps
    rr = real_roots(qc)
    print("q =", qc)
    print("roots:", np.sort(rr.real), "max imag:", np.max(np.abs(rr.imag)))
    q, eqs, R1, R2 = make_system(qc)
    print("num eqs", len(eqs))
    # degree info
    for i, e in enumerate(eqs):
        print("  eq", i, "total degree", sp.Poly(e, *vars_).total_degree(),
              "terms", len(sp.Poly(e, *vars_).terms()))
    sols = solve_numeric(eqs, n_starts=400, seed=1)
    print("distinct numeric solutions:", len(sols))
    for x, val in sols:
        print("  resid %.2e  a,b,c=%.6f,%.6f,%.6f  p,q,r=%.6f,%.6f,%.6f  Delta=%.6f"
              % (val, x[0], x[1], x[2], x[3], x[4], x[5], x[6]))


if __name__ == '__main__':
    main()
