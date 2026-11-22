"""Session 24: lines that are flex tangents of two members of a pencil of plane cubics.

For a pencil t*A + s*B of ternary cubics, a line L is a flex tangent of the member
(s:t) iff (t*A + s*B)|_L is a cube, i.e. its binary Hessian vanishes. L is a
"two-cube line" iff this happens for two distinct members. Lines are written
z = alpha*x + beta*y (a generic chart; z = 0 is alpha = beta = 0).

Usage:
  python3 pencil_flex.py random <seed> <starts>   count two-cube lines of a random pencil
  python3 pencil_flex.py fact5 <seed> <starts>    pencil of a random fact 5 configuration:
        A = X^3 + lam X^2 Z + Y^2 Z (singular), B = implicit equation of t -> (U(t), V(t)).
        Expect z = 0 among the solutions, with members (s:t) = (0:1) and (1:0).
"""
import sys, itertools
import numpy as np
import sympy as sp

x, y, z, T = sp.symbols('x y z T')


def bin_coeffs(F, al, be):
    """coefficients c0..c3 of F(x, y, al x + be y) in x^3, x^2 y, x y^2, y^3 (numeric)."""
    return F(al, be)


def make_restrictor(Fexpr):
    al, be = sp.symbols('al be')
    G = sp.expand(Fexpr.subs(z, al * x + be * y))
    P = sp.Poly(G, x, y)
    cs = [P.coeff_monomial(x**3), P.coeff_monomial(x**2 * y), P.coeff_monomial(x * y**2), P.coeff_monomial(y**3)]
    f = sp.lambdify((al, be), cs, 'numpy')
    return lambda a, b: np.array(f(a, b), dtype=complex)


def hess(c):
    c0, c1, c2, c3 = c
    return np.array([3 * c0 * c2 - c1**2, 9 * c0 * c3 - c1 * c2, 3 * c1 * c3 - c2**2])


def matrix(ra, rb, al, be):
    a = ra(al, be); b = rb(al, be)
    # Hessian of t a + s b is quadratic in (s, t): columns s^2, s t, t^2
    h_ss = hess(b)                      # s^2 part
    h_tt = hess(a)                      # t^2 part
    h_st = hess(a + b) - h_ss - h_tt     # cross part (bilinear)
    return np.stack([h_ss, h_st, h_tt], axis=1)  # rows: Hessian coeffs, cols: s^2, st, t^2


def minors(M):
    out = []
    for (i, j) in itertools.combinations(range(3), 2):
        for (k, l) in itertools.combinations(range(3), 2):
            out.append(M[i, k] * M[j, l] - M[i, l] * M[j, k])
    return np.array(out)


def residual(ra, rb, v):
    M = matrix(ra, rb, v[0], v[1])
    sc = np.linalg.norm(M) ** 2 + 1e-300
    return minors(M) / sc


def solve(ra, rb, starts, rng):
    sols = []
    for _ in range(starts):
        v = rng.normal(size=2) + 1j * rng.normal(size=2)
        lam = 1e-3
        ok = False
        for it in range(200):
            r = residual(ra, rb, v)
            J = np.zeros((len(r), 2), dtype=complex)
            h = 1e-7
            for k in range(2):
                dv = np.zeros(2, dtype=complex); dv[k] = h
                J[:, k] = (residual(ra, rb, v + dv) - r) / h
            A = J.conj().T @ J + lam * np.eye(2)
            step = np.linalg.solve(A, -J.conj().T @ r)
            vn = v + step
            if np.linalg.norm(residual(ra, rb, vn)) < np.linalg.norm(r):
                v = vn; lam = max(lam / 3, 1e-12)
            else:
                lam *= 10
            if np.linalg.norm(r) < 1e-13 or abs(v[0]) > 1e6:
                ok = np.linalg.norm(r) < 1e-13
                break
        if ok:
            sols.append(v)
    # dedupe
    uniq = []
    for s in sols:
        if all(np.linalg.norm(s - u) > 1e-6 for u in uniq):
            uniq.append(s)
    return uniq


def members(ra, rb, v):
    """the two members (s:t) whose restriction is a cube; returns the common quadratic in (s,t)."""
    M = matrix(ra, rb, v[0], v[1])
    k = np.argmax(np.linalg.norm(M, axis=1))
    q = M[k]  # coefficients of s^2, st, t^2
    disc = q[1]**2 - 4 * q[0] * q[2]
    return q, disc


def run(Aexpr, Bexpr, starts, seed, label):
    rng = np.random.default_rng(seed)
    ra, rb = make_restrictor(Aexpr), make_restrictor(Bexpr)
    sols = solve(ra, rb, starts, rng)
    good = []
    for v in sols:
        q, disc = members(ra, rb, v)
        good.append((v, q, disc))
    print(f"{label}: {len(good)} distinct solutions from {starts} starts")
    for v, q, disc in sorted(good, key=lambda w: abs(w[0][0]) + abs(w[0][1])):
        print(f"  alpha={v[0]:.6f} beta={v[1]:.6f}  |disc of member quadratic|={abs(disc):.2e}  real={np.allclose(v.imag,0,atol=1e-8)}")
    return good


if __name__ == '__main__':
    mode, seed, starts = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rs = np.random.default_rng(seed)
    if mode == 'random':
        mons = [x**i * y**j * z**(3 - i - j) for i in range(4) for j in range(4 - i)]
        A = sum(int(rs.integers(-9, 10)) * m for m in mons)
        B = sum(int(rs.integers(-9, 10)) * m for m in mons)
        run(A, B, starts, seed, 'random pencil')
    else:
        lam = sp.Rational(int(rs.integers(1, 9)), int(rs.integers(1, 5)))
        u = [sp.Integer(int(rs.integers(-5, 6))) for _ in range(2)]
        vv = [sp.Integer(int(rs.integers(-5, 6))) for _ in range(4)]
        U = T**3 + u[0] * T + u[1]
        V = vv[0] * T**3 + vv[1] * T**2 + vv[2] * T + vv[3]
        X, Y = sp.symbols('X Y')
        Gam = sp.resultant(X - U, Y - V, T)          # implicit affine equation of Gamma
        Gh = sp.expand(sp.Poly(Gam, X, Y).homogenize(z).as_expr().subs({X: x, Y: y}))
        Eh = x**3 + lam * x**2 * z + y**2 * z
        m = sp.expand(U**3 + lam * U**2 + V**2)
        print('fact 5 nonic:', sp.factor(m))
        run(Eh, Gh, starts, seed, 'fact 5 pencil')
