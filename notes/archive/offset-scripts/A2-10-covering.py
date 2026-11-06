"""A2-10-covering: F1 line-family cofactor system Q = P*g.

Normal form: Q = u^2(u'^2+v'^2) - D^2 v'^2, u cubic, v' quadratic.
For target degree n, g is monic of degree 10-n; unknowns = 8 + (10-n); equations = 11.
  n=7 -> 11 unknowns (square), n=6 -> 12, n=5 -> 13.
Validation: real solutions should appear for n small (positive-dimensional fibre), which
makes a negative result at n=7 credible rather than a solver artefact.
"""
import numpy as np
import sympy as sp
from scipy.optimize import least_squares

t = sp.symbols('t')
a0, a1, a2, a3, b0, b1, b2, D = sp.symbols('a0 a1 a2 a3 b0 b1 b2 D')
u = a3 * t ** 3 + a2 * t ** 2 + a1 * t + a0
vp = b2 * t ** 2 + b1 * t + b0
Q = sp.expand(u ** 2 * (sp.diff(u, t) ** 2 + vp ** 2) - D ** 2 * vp ** 2)


def make(n):
    gsym = sp.symbols('g0:%d' % (10 - n))
    G = t ** (10 - n) + sum(gsym[k] * t ** k for k in range(10 - n))
    P = t ** n + sum(sp.Rational((k * 7) % 5 - 2, (k % 3) + 1) * t ** k for k in range(n))
    diff = sp.expand(Q - G * P)
    coeffs = [sp.expand(diff.coeff(t, k)) for k in range(11)]
    args = (a0, a1, a2, a3, b0, b1, b2, D) + tuple(gsym)
    return P, sp.lambdify(args, coeffs, 'numpy'), len(args)


def scan(n, starts=3000, seed=7):
    P, f, nv = make(n)
    rng = np.random.default_rng(seed)
    sols = []
    for i in range(starts):
        x0 = rng.normal(0, 1.0, nv)
        try:
            r = least_squares(f, x0, xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=1000)
        except Exception:
            continue
        if np.max(np.abs(r.fun)) < 1e-9:
            x = r.x
            if all(np.linalg.norm(x - s) > 1e-5 for s in sols):
                sols.append(x)
    print('n=%d  unknowns=%d  distinct real solutions=%d' % (n, nv, len(sols)))
    for x in sols[:5]:
        print('   D=%.4f a=(%.3f,%.3f,%.3f,%.3f)' % (x[7], x[0], x[1], x[2], x[3]))


if __name__ == '__main__':
    for n in (4, 5, 6, 7):
        scan(n)
