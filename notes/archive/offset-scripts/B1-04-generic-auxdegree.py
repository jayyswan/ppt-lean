"""B1-04: auxiliary degree for a generic totally real septic (large Galois group).

Builds the covering system W mod q = 0 for a rational septic q, refines real
solutions to 200 digits, and searches (PSLQ) for the minimal polynomial of the
unknowns.  Also samples Frobenius cycle types q mod p as Galois evidence.
"""
import sys
import numpy as np
import sympy as sp
import mpmath as mp
from scipy.optimize import root

mp.mp.dps = 200

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)


def galois_evidence(qcoeffs, primes=(3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)):
    q = sum(int(co) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    pats = {}
    for pr in primes:
        qp = sp.Poly(q, t, modulus=pr)
        fl = qp.factor_list()
        degs = tuple(sorted((f.degree() for f, _ in fl[1]), reverse=True))
        pats.setdefault(degs, []).append(pr)
    return pats


def build(qcoeffs):
    q = sum(sp.Integer(int(co)) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    u = t ** 3 + a * t ** 2 + b * t + c
    up = sp.diff(u, t)
    vp = p * t ** 2 + qq * t + r
    W = sp.expand(u ** 2 * (up ** 2 + vp ** 2) - Dlt * vp ** 2)
    _, rem = sp.div(W, q, t)
    eqs = [sp.expand(rem.coeff(t, i)) for i in range(7)]
    return eqs


def main(qcoeffs, maxdeg=18):
    qc0 = [int(v) for v in qcoeffs]
    g = 0
    for v in qc0:
        g = np.gcd(g, abs(v))
    qc = [v // g for v in qc0]
    print("q =", qc)
    pats = galois_evidence(qc)
    print("Frobenius degree patterns mod primes:", {k: v for k, v in pats.items()})
    totreal = np.all(np.abs(np.roots(qc).imag) < 1e-8)
    print("totally real:", totreal)
    eqs = build(qc)
    f_np = sp.lambdify(vars_, eqs, 'numpy')
    J = sp.Matrix(eqs).jacobian(vars_)
    f_mp_i = [sp.lambdify(vars_, eqs[i], 'mpmath') for i in range(7)]
    J_mp = [[sp.lambdify(vars_, J[i, j], 'mpmath') for j in range(7)] for i in range(7)]

    rng = np.random.default_rng(11)
    sols = []
    for s in range(800):
        x0 = rng.normal(size=7) * np.array([2., 4., 4., 2., 4., 4., 4.])
        res = root(lambda x: np.asarray(f_np(*x), float), x0, method='hybr',
                   options={'maxfev': 4000})
        if res.success and np.max(np.abs(np.asarray(f_np(*res.x), float))) < 1e-7:
            xs = res.x.copy(); xs[3:6] *= -1
            if not any(np.max(np.abs(res.x - y)) < 1e-5 for y in sols):
                sols.append(res.x)
    print("real solutions (mod v' sign):", len(sols))

    def refine(x0):
        x = [mp.mpf(v) for v in x0]
        F = None
        for it in range(80):
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
            if max(abs(F[i]) for i in range(7)) < mp.mpf('1e-180'):
                break
        return x

    def min_poly(val, maxdeg=maxdeg):
        P = mp.mpf(val)
        for d in range(1, maxdeg + 1):
            vec = [P ** k for k in range(d + 1)]
            rel = mp.pslq(vec, maxcoeff=10 ** 70, maxsteps=20000, tol=mp.mpf('1e-180'))
            if rel is not None and rel[-1] != 0:
                s = sum(mp.mpf(co) * P ** k for k, co in enumerate(rel))
                if abs(s) < mp.mpf('1e-120'):
                    return d, rel
        return None, None

    seen = set()
    out = []
    for x0 in sols:
        xr = refine(x0)
        if xr is None:
            continue
        key = round(float(xr[6]), 8)
        if key in seen:
            continue
        seen.add(key)
        dD, pD = min_poly(xr[6])
        da, pa = min_poly(xr[0])
        out.append((xr, dD, pD, da, pa))
        print("Delta=%.12f  resid=%.1e  deg(Delta)=%s  deg(a)=%s"
              % (float(xr[6]), float(max(abs(f_mp_i[i](*xr)) for i in range(7))), dD, da),
              flush=True)
    print("\nDistinct deg(Delta) values:", sorted(set(str(o[1]) for o in out)))
    print("Distinct deg(a) values:", sorted(set(str(o[3]) for o in out)))
    for (xr, dD, pD, da, pa) in out[:3]:
        if pD:
            print("minpoly(Delta) example:", pD, "  (verified)")


if __name__ == '__main__':
    qc = eval(sys.argv[1]) if len(sys.argv) > 1 else [90, 12, -712, 27, 1424, 17, -667, 0]
    main(qc)

