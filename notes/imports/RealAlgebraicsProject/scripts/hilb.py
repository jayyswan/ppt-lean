"""Session 26: Hilbert-scheme chart for conics in L_135 that also covers degenerate conics.
Unknowns: plane basis E (9x3), conic q (6 coeffs), l3 (3), h3 (10).
Equations: p1|Pi = 0 (3), p3|Pi - q*l3 = 0 (10), p5|Pi - q*h3 = 0 (21): 34 equations, 46 unknowns,
gauge GL3 x scaling of q = 10.  Expected kernel of the Jacobian at a smooth point of the 2-dim family: 12."""
import numpy as np, itertools
from math import factorial
n = 9
def monos(d): return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) == d]
M = {d: monos(d) for d in range(6)}
IDX = {d: {e: i for i, e in enumerate(M[d])} for d in M}
def restrict(E, k):
    """coefficients of sum_i (E[i]·(x,y,z))^k in the monomial basis M[k]"""
    out = np.zeros(len(M[k]))
    for j, e in enumerate(M[k]):
        c = factorial(k) / (factorial(e[0]) * factorial(e[1]) * factorial(e[2]))
        out[j] = c * np.sum(E[:, 0]**e[0] * E[:, 1]**e[1] * E[:, 2]**e[2])
    return out
def mul(A, da, B, db):
    out = np.zeros(len(M[da + db]))
    for i, e in enumerate(M[da]):
        for j, f in enumerate(M[db]):
            out[IDX[da + db][(e[0] + f[0], e[1] + f[1], e[2] + f[2])]] += A[i] * B[j]
    return out
def F(u):
    E = u[:27].reshape(9, 3); q = u[27:33]; l3 = u[33:36]; h3 = u[36:46]
    return np.concatenate([restrict(E, 1), restrict(E, 3) - mul(q, 2, l3, 1), restrict(E, 5) - mul(q, 2, h3, 3)])
def jac(u, h=1e-6):
    return np.array([(F(u + h * ei) - F(u - h * ei)) / (2 * h) for ei in np.eye(len(u))]).T
def fit_lh(E, q):
    """least-squares l3, h3 given E, q"""
    A3 = np.array([mul(q, 2, ei, 1) for ei in np.eye(3)]).T
    A5 = np.array([mul(q, 2, ei, 3) for ei in np.eye(10)]).T
    l3 = np.linalg.lstsq(A3, restrict(E, 3), rcond=None)[0]
    h3 = np.linalg.lstsq(A5, restrict(E, 5), rcond=None)[0]
    return l3, h3, np.linalg.norm(A3 @ l3 - restrict(E, 3)), np.linalg.norm(A5 @ h3 - restrict(E, 5))
def kernel_dim(u, tol=1e-6):
    s = np.linalg.svd(jac(u), compute_uv=False)
    return 46 - np.sum(s > tol * s[0]), s
def p5_on_line(E, l):
    """relative size of p5 restricted to the line {l·(x,y,z) = 0} in the plane"""
    B = np.linalg.svd(l.reshape(1, 3))[2][1:]
    m0, m1 = E @ B[0], E @ B[1]
    ts = np.linspace(-1, 1, 7)
    c = np.polyfit(ts, [np.sum((m0 + t * m1)**5) for t in ts], 5)
    sc = np.polyfit(ts, [np.sum(np.abs(m0 + t * m1)**5) for t in ts], 5)
    return np.max(np.abs(c)) / np.max(np.abs(sc))
