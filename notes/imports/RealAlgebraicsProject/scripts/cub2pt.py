#!/usr/bin/env python3
"""Session 54: twisted cubics through two general complex points Q1, Q2 of
V_S (default S = 2,4 inside {Tr = 0}, i.e. V_124), q(k) = Q1 + k u + k^2 v + k^3 Q2,
u, v in {Tr = 0}.  Equations: coefficients k^1 .. k^{3d-1} of p_d(q) for d in S
(16 equations, 16 unknowns for S = 2,4).  Solutions come in mu_3-orbits
(u, v) -> (w u, w^2 v); counted modulo mu_3.  Random-start damped Newton;
prints the number of distinct nondegenerate curves every 250 starts.
usage: cub2pt.py <seed> <starts> [S=2,4]
"""
import sys, numpy as np

n = 9

def basis0():
    B = np.zeros((n, n - 1))
    for i in range(n - 1):
        B[i, i] = 1; B[n - 1, i] = -1
    return B

def coeffs(As, d):
    e = len(As) - 1
    N = e * d + 1
    k = np.exp(2j * np.pi * np.arange(N) / N)
    q = sum((k ** j)[:, None] * As[j][None, :] for j in range(e + 1))
    val = (q ** d).sum(1)
    der = d * q ** (d - 1)
    W = np.exp(-2j * np.pi * np.outer(np.arange(N), np.arange(N)) / N) / N
    return W @ val, [W @ (der * (k ** j)[:, None]) for j in range(e + 1)]

def point(rng, S):
    """generic complex point of V_S in {Tr = 0} (min-norm Newton)."""
    B = basis0()
    for _ in range(50):
        x = rng.standard_normal(n - 1) + 1j * rng.standard_normal(n - 1)
        for it in range(100):
            y = B @ x
            f = np.array([np.sum(y ** d) for d in S])
            Jm = np.array([d * (y ** (d - 1)) @ B for d in S])
            x = x - np.linalg.pinv(Jm) @ f
            if np.linalg.norm(f) < 1e-14 * np.linalg.norm(x) ** 4: break
        y = B @ x
        if max(abs(np.sum(y ** d)) for d in S) < 1e-12 * np.linalg.norm(y) ** 4:
            return y / np.linalg.norm(y)
    raise RuntimeError

def system(Q1, Q2, S):
    B = basis0()
    def F(x):
        u = B @ x[:8]; v = B @ x[8:]
        out = []
        for d in S:
            c, _ = coeffs([Q1, u, v, Q2], d)
            out.append(c[1:3 * d])
        return np.concatenate(out)
    def J(x):
        u = B @ x[:8]; v = B @ x[8:]
        rows = []
        for d in S:
            c, Js = coeffs([Q1, u, v, Q2], d)
            rows.append(np.hstack([Js[1][1:3 * d] @ B, Js[2][1:3 * d] @ B]))
        return np.vstack(rows)
    return F, J

def newton(F, J, x, it=80):
    for _ in range(it):
        f = F(x)
        try:
            dx = np.linalg.solve(J(x), f)
        except np.linalg.LinAlgError:
            return None
        t = 1.0
        nf = np.linalg.norm(f)
        while t > 1e-4:
            xn = x - t * dx
            if np.linalg.norm(F(xn)) < nf: break
            t /= 2
        x = xn
        if np.linalg.norm(F(x)) < 1e-13 * (1 + np.linalg.norm(x)) ** 4:
            return x
        if not np.all(np.isfinite(x)) or np.linalg.norm(x) > 1e6: return None
    return None

def canon(x):
    u = x[:8]
    j = int(np.argmax(np.abs(u)))
    w = np.exp(2j * np.pi / 3)
    best = None
    for k in range(3):
        uu = u * w ** k; vv = x[8:] * w ** (2 * k)
        a = np.angle(uu[j]) % (2 * np.pi)
        if a < 2 * np.pi / 3 + 1e-9:
            best = np.concatenate([uu, vv])
    return best

def main():
    seed = int(sys.argv[1]); starts = int(sys.argv[2])
    S = [int(t) for t in sys.argv[3].split(',')] if len(sys.argv) > 3 else [2, 4]
    rng = np.random.default_rng(seed)
    Q1 = point(rng, S); Q2 = point(rng, S)
    F, J = system(Q1, Q2, S)
    B = basis0()
    sols = []
    for st in range(1, starts + 1):
        sc = rng.uniform(0.3, 3)
        x0 = sc * (rng.standard_normal(16) + 1j * rng.standard_normal(16))
        x = newton(F, J, x0)
        if x is not None:
            # nondegenerate: Q1, u, v, Q2 span a 3-space; Jacobian nonsingular
            R = np.vstack([Q1, B @ x[:8], B @ x[8:], Q2])
            sv = np.linalg.svd(R, compute_uv=False)
            cJ = np.linalg.cond(J(x))
            if sv[-1] / sv[0] > 1e-6 and cJ < 1e10:
                c = canon(x)
                if not any(np.linalg.norm(c - s) < 1e-6 * (1 + np.linalg.norm(c)) for s in sols):
                    sols.append(c)
        if st % 250 == 0:
            print(f'starts={st} distinct curves={len(sols)}', flush=True)
    np.save(f'cub2pt_{seed}.npy', np.array(sols))

if __name__ == '__main__':
    main()
