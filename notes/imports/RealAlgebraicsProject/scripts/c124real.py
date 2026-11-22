#!/usr/bin/env python3
"""Session 53: real conics q = A + B k + C k^2 in K (x) R = R^r x C^s (n = 9) with
p_d(q) == 0 identically for d in S (default S = 1,2,4: V_124), found by
Levenberg-Marquardt (scipy least_squares, analytic Jacobian) with 4 random affine
gauge rows.  For each solution: residual, rank of [A,B,C], number of distinct
classes [A_i:B_i:C_i] in P^2 among the 9 coordinates, trace signature on <A,B,C>,
and the real-root count / sign changes of p_last(q(k)) (default last = 3).
usage: c124real.py <r> <starts> <seed> [S=1,2,4] [last=3]
"""
import sys, numpy as np
from scipy.optimize import least_squares

n = 9

def coordmap(r):
    s = (n - r) // 2
    M = np.zeros((n, n), complex)
    for i in range(r):
        M[i, i] = 1
    for j in range(s):
        a, b = r + 2 * j, r + 2 * j + 1
        M[a, a] = 1; M[a, b] = 1j
        M[b, a] = 1; M[b, b] = -1j
    return M

def coeffs(Ac, Bc, Cc, d):
    """coefficients (deg 0..2d) of sum_i (A_i + B_i k + C_i k^2)^d, and the
    Jacobian blocks wrt A, B, C (complex coordinates)."""
    N = 2 * d + 1
    k = np.exp(2j * np.pi * np.arange(N) / N)
    q = Ac[None, :] + k[:, None] * Bc[None, :] + (k ** 2)[:, None] * Cc[None, :]
    val = (q ** d).sum(1)
    der = d * q ** (d - 1)                      # N x n
    # coefficients c_m = (1/N) sum_j val_j k_j^{-m}
    W = np.exp(-2j * np.pi * np.outer(np.arange(N), np.arange(N)) / N) / N
    c = W @ val
    JA = W @ der
    JB = W @ (der * k[:, None])
    JC = W @ (der * (k ** 2)[:, None])
    return c, JA, JB, JC

def make(r, S, G, g):
    M = coordmap(r)
    def F(x):
        A, B, C = (M @ x[:9], M @ x[9:18], M @ x[18:])
        out = []
        for d in S:
            c, *_ = coeffs(A, B, C, d)
            out.append(c.real)
        out.append(G @ x - g)
        return np.concatenate(out)
    def J(x):
        A, B, C = (M @ x[:9], M @ x[9:18], M @ x[18:])
        rows = []
        for d in S:
            c, JA, JB, JC = coeffs(A, B, C, d)
            rows.append(np.hstack([(JA @ M).real, (JB @ M).real, (JC @ M).real]))
        rows.append(G)
        return np.vstack(rows)
    return M, F, J

def analyse(x, M, last):
    A, B, C = (M @ x[:9], M @ x[9:18], M @ x[18:])
    R = np.vstack([x[:9], x[9:18], x[18:]])
    sv = np.linalg.svd(R, compute_uv=False)
    # classes in P^2 of (A_i, B_i, C_i)
    P = np.vstack([A, B, C]).T
    P = P / np.linalg.norm(P, axis=1)[:, None]
    cls = []
    for p in P:
        if not any(abs(abs(np.vdot(p, c)) - 1) < 1e-6 for c in cls):
            cls.append(p)
    # trace form on span(A,B,C): T(y,z) = sum (M y)_i (M z)_i
    V = [A, B, C]
    T = np.array([[np.sum(a * b).real for b in V] for a in V])
    ev = np.linalg.eigvalsh(T)
    sig = (int((ev > 1e-8 * abs(ev).max()).sum()), int((ev < -1e-8 * abs(ev).max()).sum()))
    c, *_ = coeffs(A, B, C, last)
    pc = c.real
    roots = np.roots(pc[::-1])
    nreal = int(sum(abs(rt.imag) < 1e-7 * (1 + abs(rt)) for rt in roots))
    # sign changes on a grid in the projective parameter (k = tan theta)
    th = np.linspace(-np.pi / 2 + 1e-4, np.pi / 2 - 1e-4, 20001)
    kk = np.tan(th)
    vals = np.polyval(pc[::-1], kk) * np.cos(th) ** (2 * last)
    ch = int(np.sum(np.sign(vals[1:]) != np.sign(vals[:-1])))
    norm = np.max(np.abs(vals))
    return sv, len(cls), sig, nreal, ch, np.min(np.abs(vals)) / norm, pc

def gn(F, J, x, it=300):
    lam = 1e-3
    f = F(x); nf = np.linalg.norm(f)
    for _ in range(it):
        Jx = J(x)
        # damped minimum-norm step
        JJ = Jx @ Jx.T
        step = Jx.T @ np.linalg.solve(JJ + lam * np.eye(len(f)), f)
        xn = x - step; fn = F(xn); nn = np.linalg.norm(fn)
        if np.isfinite(nn) and nn < nf:
            x, f, nf = xn, fn, nn; lam = max(lam / 3, 1e-14)
        else:
            lam *= 4
            if lam > 1e8: break
        if nf < 1e-14 * (1 + np.linalg.norm(x) ** 4): break
    return x

def main():
    r = int(sys.argv[1]); starts = int(sys.argv[2]); seed = int(sys.argv[3])
    S = [int(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [1, 2, 4]
    last = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    rng = np.random.default_rng(seed)
    tally = {}
    for st in range(starts):
        G = rng.standard_normal((4, 27)); g = rng.standard_normal(4)
        M, F, J = make(r, S, G, g)
        x0 = rng.standard_normal(27)
        x = gn(F, J, x0)
        res = np.linalg.norm(F(x)) / (1 + np.linalg.norm(x) ** 4)
        if res > 1e-10:
            print(f'{st}: no convergence res={res:.1e}'); continue
        sv, ncls, sig, nreal, ch, mn, pc = analyse(x, M, last)
        Jr = np.linalg.matrix_rank(J(x), tol=1e-7 * np.linalg.norm(J(x)))
        deg = sv[2] / sv[0] < 1e-6
        key = ('degenerate' if deg else f'cls={ncls} sig={sig} p{last}-signchanges={ch}')
        tally[key] = tally.get(key, 0) + 1
        print(f'{st}: res={res:.1e} sv={sv[2]/sv[0]:.2e} classes={ncls} sig={sig} '
              f'Jrank={Jr} p{last} real roots={nreal} sign changes={ch} min|p|/max={mn:.2e}')
    print('tally:', tally)

if __name__ == '__main__':
    main()
