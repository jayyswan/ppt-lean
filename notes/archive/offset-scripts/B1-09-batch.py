"""B1-09: batch auxiliary-degree measurement with the well-conditioned root-based
system.  For each rational totally real septic, solve
  F_i = u(r_i)^2 (u'(r_i)^2 + v'(r_i)^2) - Delta v'(r_i)^2 = 0   (i=1..7),
refine to 200 digits, PSLQ the minimal polynomials of Delta and a.
"""
import numpy as np
import mpmath as mp
from scipy.optimize import root
import sympy as sp

mp.mp.dps = 200


def get_roots(qc):
    rr = np.roots([float(v) for v in qc])
    if np.max(np.abs(rr.imag)) > 1e-6:
        raise ValueError("not totally real")
    return [mp.mpf(float(x.real)) for x in rr]


def make_F(roots):
    roots = [mp.mpf(x) for x in roots]

    def F(x):
        a, b, c, p, qq, r, Dlt = x
        out = []
        for ri in roots:
            u = ri**3 + a * ri**2 + b * ri + c
            up = 3 * ri**2 + 2 * a * ri + b
            vp = p * ri**2 + qq * ri + r
            out.append(u * u * (up * up + vp * vp) - Dlt * vp * vp)
        return out
    return F


def make_J(roots):
    roots = [mp.mpf(x) for x in roots]

    def J(x):
        a, b, c, p, qq, r, Dlt = x
        M = mp.matrix(7, 7)
        for i, ri in enumerate(roots):
            u = ri**3 + a * ri**2 + b * ri + c
            up = 3 * ri**2 + 2 * a * ri + b
            vp = p * ri**2 + qq * ri + r
            S = up**2 + vp**2
            # d/da, d/db, d/dc
            M[i, 0] = 2 * u * ri**2 * S + u**2 * 2 * up * (2 * ri)
            M[i, 1] = 2 * u * ri * S + u**2 * 2 * up * 1
            M[i, 2] = 2 * u * S + u**2 * 0
            # d/dp, d/dqq, d/dr
            M[i, 3] = u**2 * 2 * vp * ri**2 - Dlt * 2 * vp * ri**2
            M[i, 4] = u**2 * 2 * vp * ri - Dlt * 2 * vp * ri
            M[i, 5] = u**2 * 2 * vp - Dlt * 2 * vp
            M[i, 6] = -vp**2
        return M
    return J


def solve(qc, n_starts=1200, seed=0):
    rmp = get_roots(qc)
    roots_np = np.array([complex(x) for x in rmp])
    roots_real = np.array([float(x.real) for x in rmp])  # q totally real
    F = make_F([float(x.real) for x in rmp])
    J = make_J([float(x.real) for x in rmp])
    Fnp = lambda x: np.array([float(v) for v in F([mp.mpf(v) for v in x])])
    Jnp = lambda x: np.array([[float(J([mp.mpf(v) for v in x])[i, j]) for j in range(7)] for i in range(7)])
    rng = np.random.default_rng(seed)
    sols = []
    for s in range(n_starts):
        x0 = rng.normal(size=7) * np.array([1., 2., 3., 1., 2., 3., 50.])
        try:
            res = root(Fnp, x0, jac=Jnp, method='hybr', options={'maxfev': 3000})
        except Exception:
            continue
        if res.success and np.max(np.abs(Fnp(res.x))) < 1e-8:
            xs = res.x.copy(); xs[3:6] *= -1
            if not any(np.max(np.abs(res.x - y)) < 1e-6 for y in sols):
                sols.append(res.x)
    # refine with mpmath
    Fm = F; Jm = J
    out = []
    for x0 in sols:
        x = [mp.mpf(v) for v in x0]
        for it in range(60):
            Fv = mp.matrix(Fm(x)); M = Jm(x)
            try:
                dx = mp.lu_solve(M, Fv)
            except Exception:
                x = None; break
            x = [x[i] - dx[i] for i in range(7)]
            if max(abs(Fv[i]) for i in range(7)) < mp.mpf('1e-180'):
                break
        if x is None:
            continue
        out.append(x)
    return out


def minpoly(val, maxdeg=10):
    P = mp.mpf(val)
    for d in range(1, maxdeg + 1):
        vec = [P**k for k in range(d + 1)]
        rel = mp.pslq(vec, maxcoeff=10**80, maxsteps=30000, tol=mp.mpf('1e-180'))
        if rel is not None and rel[-1] != 0:
            s = sum(mp.mpf(co) * P**k for k, co in enumerate(rel))
            if abs(s) < mp.mpf('1e-120'):
                return d
    return None


def run(name, qc):
    sols = solve(qc, n_starts=450, seed=hash(name) % 9999)
    if not sols:
        print("%-34s  NO real solutions found" % name)
        return
    degD = sorted(set(minpoly(x[6]) for x in sols))
    dega = sorted(set(minpoly(x[0]) for x in sols))
    dd = [min(x[6] for x in sols), max(x[6] for x in sols)]
    print("%-34s  n=%2d  Delta>0:%2d  deg(Delta) in %s  deg(a) in %s  Delta range [%.3f,%.3f]"
          % (name, len(sols), sum(1 for x in sols if x[6] > 0), degD, dega, dd[0], dd[1]), flush=True)


if __name__ == '__main__':
    import numpy as _np
    rng = _np.random.default_rng(99)
    q0 = _np.array([1., 0, -7, 0, 14, 0, -7, 0])
    cases = []
    tries = 0
    while len(cases) < 6 and tries < 60000:
        tries += 1
        c = q0.copy()
        for k in range(1, 8):
            c[k] += rng.integers(-15, 16)
        sh = rng.integers(-4, 5)
        cc = _np.poly1d(c)(_np.poly1d([1, sh])).c
        rr = _np.roots(cc)
        if _np.max(_np.abs(rr.imag)) < 1e-6 and max(abs(v) for v in cc) < 5000:
            ci = [int(round(v)) for v in cc]
            g = 0
            for v in ci:
                g = _np.gcd(g, abs(v))
            ci = [v // g for v in ci]
            cases.append((f"rand{len(cases)}", ci))
    for nm, qc in cases:
        run(nm, qc)


