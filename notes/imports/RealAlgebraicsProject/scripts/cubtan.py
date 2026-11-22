#!/usr/bin/env python3
"""Session 54: twisted cubics through a generic complex point Q of V_124 with a
prescribed tangent vector u (u in T_Q, generic): q = Q + k u + k^2 v + k^3 w,
v, w in {Tr = 0}; equations: coefficients k^2..k^{3d} of p_d(q), d in S
(16 x 16 for S = 2,4; no gauge left).  This is the degree of the tangent map
T_Q -> P(T_Q V) = P^4.  Random-start damped Newton; distinct nondegenerate
solutions every 250 starts (degenerate = Q, u, v, w span < 4 dims).
usage: cubtan.py <seed> <starts> [S=2,4]
"""
import sys, numpy as np
exec(open('cub2pt.py').read().split("\ndef main")[0])

def main():
    seed = int(sys.argv[1]); starts = int(sys.argv[2])
    S = [int(t) for t in sys.argv[3].split(',')] if len(sys.argv) > 3 else [2, 4]
    rng = np.random.default_rng(seed)
    B = basis0()
    Q = point(rng, S)
    Jm = np.array([d * (Q ** (d - 1)) @ B for d in S])
    _, _, Vh = np.linalg.svd(Jm)
    T = Vh[len(S):].conj().T          # tangent basis (coords in trace-zero basis)
    u = B @ (T @ (rng.standard_normal(T.shape[1]) + 1j * rng.standard_normal(T.shape[1])))
    def F(x):
        v = B @ x[:8]; w = B @ x[8:]
        return np.concatenate([coeffs([Q, u, v, w], d)[0][2:3 * d + 1] for d in S])
    def J(x):
        v = B @ x[:8]; w = B @ x[8:]
        rows = []
        for d in S:
            c, Js = coeffs([Q, u, v, w], d)
            rows.append(np.hstack([Js[2][2:3 * d + 1] @ B, Js[3][2:3 * d + 1] @ B]))
        return np.vstack(rows)
    print('check u tangent:', [abs(np.sum(d * Q ** (d - 1) * u)) for d in S])
    sols = []
    for st in range(1, starts + 1):
        sc = rng.uniform(0.3, 3)
        x = newton(F, J, sc * (rng.standard_normal(16) + 1j * rng.standard_normal(16)))
        if x is not None:
            R = np.vstack([Q, u, B @ x[:8], B @ x[8:]])
            sv = np.linalg.svd(R, compute_uv=False)
            if sv[-1] / sv[0] > 1e-6 and np.linalg.cond(J(x)) < 1e10:
                if not any(np.linalg.norm(x - s) < 1e-6 * (1 + np.linalg.norm(x)) for s in sols):
                    sols.append(x)
        if st % 250 == 0:
            print(f'starts={st} distinct={len(sols)}', flush=True)

if __name__ == '__main__':
    main()
