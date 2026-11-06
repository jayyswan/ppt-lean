"""B1-10: numeric-only family counts (memory-bounded, no sympy expansion).

(a) Jacobian rank of the decic line family coefficient map.
(b) degree and Jacobian rank of the offset-cubic x conic family
    W_mod = (F(gamma)R + d^2 Q)^2 - d^2 R L^2   (degree 20).
(c) calibration: decic covering of a totally real quintic / sextic (underdetermined).

Polynomials are coefficient arrays in ASCENDING powers (numpy.polynomial).
"""
import numpy as np
from scipy.optimize import least_squares


def pmul(a, b):
    return np.polynomial.polynomial.polymul(a, b)


def padd(a, b):
    n = max(len(a), len(b))
    out = np.zeros(n)
    out[:len(a)] += a
    out[:len(b)] += b
    return out


def pder(a):
    return np.polynomial.polynomial.polyder(a)


def decic_coeffs(p):
    a, b, c, pp, qq, r, D = p
    u = np.array([c, b, a, 1.0])
    up = pder(u)
    vp = np.array([r, qq, pp])
    S = padd(pmul(up, up), pmul(vp, vp))
    W = padd(pmul(pmul(u, u), S), -D * pmul(vp, vp))
    return W  # length 11


def conic_coeffs(p):
    xs = np.array([p[3], p[2], p[1], p[0]])   # ascending: x3 const? map: x0 t^3+... 
    ys = np.array([p[7], p[6], p[5], p[4]])
    d = p[8]
    A, B, C, D, E = p[9:14]
    xp = pder(xs); yp = pder(ys)
    R = padd(pmul(xp, xp), pmul(yp, yp))
    x2 = pmul(xs, xs); xy = pmul(xs, ys); y2 = pmul(ys, ys)
    Fg = padd(padd(A * x2, B * xy), C * y2)
    Fg = padd(padd(Fg, D * xs), E * ys)
    Fg = padd(Fg, np.array([1.0]))
    L = padd(pmul(-(2 * A * xs + B * ys + D), yp), pmul(B * xs + 2 * C * ys + E, xp))
    Q = padd(pmul(A * yp, yp), -B * pmul(xp, yp))
    Q = padd(Q, C * pmul(xp, xp))
    inner = padd(pmul(Fg, R), d * d * Q)
    Wc = padd(pmul(inner, inner), -(d * d) * pmul(R, pmul(L, L)))
    return Wc  # length 21


def jac_rank(func, x0, label):
    x0 = np.array(x0, float)
    f0 = func(x0)
    J = np.zeros((len(f0), len(x0)))
    for j in range(len(x0)):
        h = 1e-6 * max(1.0, abs(x0[j]))
        xp = x0.copy(); xp[j] += h
        xm = x0.copy(); xm[j] -= h
        J[:, j] = (func(xp) - func(xm)) / (2 * h)
    s = np.linalg.svd(J, compute_uv=False)
    r = int(np.sum(s > 1e-7 * s[0]))
    print("%s: coeffs=%d params=%d rank=%d -> image dim (mod scaling) ~ %d"
          % (label, len(f0), len(x0), r, r - 1))
    print("   top singular values:", np.round(s[:min(16, len(s))], 4))
    return r


def calibrate(nroots, seed):
    rng = np.random.default_rng(seed)
    roots = np.sort(rng.uniform(-3, 3, nroots))

    def F(x):
        a, b, c, pp, qq, r, D = x
        return np.array([
            (ri**3 + a * ri**2 + b * ri + c)**2
            * ((3 * ri**2 + 2 * a * ri + b)**2 + (pp * ri**2 + qq * ri + r)**2)
            - D * (pp * ri**2 + qq * ri + r)**2
            for ri in roots])
    found = 0
    for _ in range(300):
        x0 = rng.normal(size=7) * np.array([1., 2., 3., 1., 2., 3., 50.])
        try:
            res = least_squares(F, x0, xtol=1e-14, ftol=1e-14)
        except Exception:
            continue
        if np.max(np.abs(F(res.x))) < 1e-8 and res.x[6] > 1e-6:
            found += 1
    print("calibration degree-%d: starts with residual<1e-8 and Delta>0: %d/300"
          % (nroots, found))


if __name__ == '__main__':
    dec = [0.3, -0.4, 0.14, 0.67, -0.25, 0.6, 2.5]
    jac_rank(decic_coeffs, dec, "decic line family")
    con = [0.5, -0.33, 0.4, 0.14, -0.67, 0.2, -0.25, 0.43, 0.67,
           0.5, -0.2, 0.33, 0.29, -0.17]
    W = conic_coeffs(con)
    print("offset-cubic x conic: composite degree =", len(W) - 1)
    jac_rank(conic_coeffs, con, "offset-cubic x conic")
    calibrate(5, 11)
    calibrate(6, 12)
