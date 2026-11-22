#!/usr/bin/env python3
"""Session 54: real rational curves q(k) = sum_{j=0}^e A_j k^j of degree e in
K (x) R = R^r x C^s (n = 9) with p_d(q) == 0 identically for d in S
(default S = 1,2,4: V_124), by damped minimum-norm Gauss-Newton with 4 random
affine gauge rows (PGL2 + scale).  Coefficients and Jacobian by DFT.
Per solution: residual, smallest normalised singular value of [A_0..A_e],
number of distinct coordinate classes in P^e, Jacobian rank, number of REAL
roots of p_last(q(k)) (degree e*last), then a tally of real-root counts.
usage: crvreal.py <r> <starts> <seed> [e=3] [S=1,2,4] [last=3]
"""
import sys, numpy as np

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

def coeffs(As, d):
    """As: list of e+1 complex n-vectors.  Coefficients (deg 0..e*d) of
    sum_i q_i(k)^d and Jacobian blocks wrt each A_j."""
    e = len(As) - 1
    N = e * d + 1
    k = np.exp(2j * np.pi * np.arange(N) / N)
    q = sum((k ** j)[:, None] * As[j][None, :] for j in range(e + 1))
    val = (q ** d).sum(1)
    der = d * q ** (d - 1)
    W = np.exp(-2j * np.pi * np.outer(np.arange(N), np.arange(N)) / N) / N
    return W @ val, [W @ (der * (k ** j)[:, None]) for j in range(e + 1)]

def make(r, e, S, G, g):
    M = coordmap(r)
    def split(x):
        return [M @ x[9 * j:9 * j + 9] for j in range(e + 1)]
    def F(x):
        As = split(x)
        out = [coeffs(As, d)[0].real for d in S]
        out.append(G @ x - g)
        return np.concatenate(out)
    def J(x):
        As = split(x)
        rows = []
        for d in S:
            _, Js = coeffs(As, d)
            rows.append(np.hstack([(Jj @ M).real for Jj in Js]))
        rows.append(G)
        return np.vstack(rows)
    return M, split, F, J

def gn(F, J, x, it=int(__import__("os").environ.get("GNIT","400"))):
    lam = 1e-3
    f = F(x); nf = np.linalg.norm(f)
    for _ in range(it):
        Jx = J(x)
        step = Jx.T @ np.linalg.solve(Jx @ Jx.T + lam * np.eye(len(f)), f)
        xn = x - step; fn = F(xn); nn = np.linalg.norm(fn)
        if np.isfinite(nn) and nn < nf:
            x, f, nf = xn, fn, nn; lam = max(lam / 3, 1e-14)
        else:
            lam *= 4
            if lam > 1e8: break
        if nf < 1e-14 * (1 + np.linalg.norm(x) ** 4): break
    return x

def nreal_roots(pc):
    pc = np.array(pc, float)
    sc = np.max(np.abs(pc))
    # projective: count roots of the binary form; drop leading zeros = roots at oo
    inf = 0
    while abs(pc[-1]) < 1e-12 * sc:
        pc = pc[:-1]; inf += 1
    rts = np.roots(pc[::-1])
    return inf + int(sum(abs(z.imag) < 1e-6 * (1 + abs(z)) for z in rts))

def main():
    r = int(sys.argv[1]); starts = int(sys.argv[2]); seed = int(sys.argv[3])
    e = int(sys.argv[4]) if len(sys.argv) > 4 else 3
    S = [int(t) for t in sys.argv[5].split(',')] if len(sys.argv) > 5 else [1, 2, 4]
    last = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    rng = np.random.default_rng(seed)
    m = 9 * (e + 1)
    tally = {}
    for st in range(starts):
        G = rng.standard_normal((4, m)); g = rng.standard_normal(4)
        M, split, F, J = make(r, e, S, G, g)
        x = gn(F, J, rng.standard_normal(m))
        res = np.linalg.norm(F(x)) / (1 + np.linalg.norm(x) ** 4)
        if not np.isfinite(res) or res > 1e-10:
            print(f'{st}: no convergence res={res:.1e}', flush=True)
            tally['noconv'] = tally.get('noconv', 0) + 1; continue
        As = split(x)
        R = np.vstack([x[9 * j:9 * j + 9] for j in range(e + 1)])
        sv = np.linalg.svd(R, compute_uv=False)
        P = np.vstack(As).T
        P = P / np.linalg.norm(P, axis=1)[:, None]
        cls = []
        for p in P:
            if not any(abs(abs(np.vdot(p, c)) - 1) < 1e-6 for c in cls):
                cls.append(p)
        Jx = J(x)
        Jr = np.linalg.matrix_rank(Jx, tol=1e-7 * np.linalg.norm(Jx))
        pc = coeffs(As, last)[0].real
        nr = nreal_roots(pc)
        deg = sv[-1] / sv[0] < 1e-6
        key = 'degenerate' if deg else f'cls={len(cls)} real p{last} roots={nr}'
        tally[key] = tally.get(key, 0) + 1
        print(f'{st}: res={res:.1e} sv={sv[-1]/sv[0]:.2e} classes={len(cls)} '
              f'Jrank={Jr}/{Jx.shape[0]} p{last} real roots={nr}', flush=True)
    print('tally:', tally)

if __name__ == '__main__':
    main()
