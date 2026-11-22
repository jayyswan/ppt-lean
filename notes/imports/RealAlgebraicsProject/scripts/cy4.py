"""Session 43: real conics in Y4 = {p1 = p3 = Q4 = 0} in P^8 (n = 9, z real = totally real twist).
Conic q(s) = A s^2 + B s + C  (affine s, t = 1), A, B, C in {sum z = 0} (8-dim basis E).
Equations: coefficients of p3(q(s)) (deg 6, 7 eqs) and Q4(q(s)) = 6 p4 - p2^2 (deg 8, 9 eqs).
Optional: shape conditions on the decic p5(q(s)) (fact-4 with quartic RHS, x^10 = quartic):
   coefficients of s^9 .. s^5 vanish (special point at s = inf, translation fixed) -> 5 eqs.
Module + main:  python3 cy4.py <seed> <starts> <mode 0|1> [out.npy]
 mode 0: conics only; mode 1: conics + shape (curve Gamma).
Gauge: random linear normalisation rows appended (4 for mode 0, 2 for mode 1) with values 1.
"""
import numpy as np, sys
from numpy.polynomial import polynomial as Pl

n = 9
E = np.linalg.qr(np.vstack([np.ones(n), np.random.RandomState(0).randn(n-1, n)]).T)[0][:, 1:]  # 9x8 orthonormal, sum 0

def qpolys(x):
    a, b, c = x[:8], x[8:16], x[16:24]
    A, B, C = E @ a, E @ b, E @ c
    return np.stack([C, B, A], axis=1)  # q_i(s) coeffs low->high, shape (9,3)

def psum(Q, k):
    tot = np.zeros(2*k+1, dtype=Q.dtype)
    for i in range(n):
        p = np.array([1.0+0j]) if np.iscomplexobj(Q) else np.array([1.0])
        for _ in range(k):
            p = Pl.polymul(p, Q[i])
        tot = tot + np.pad(p, (0, 2*k+1-len(p)))
    return tot

def eqs(x, mode):
    Q = qpolys(x)
    p2, p3, p4, p5 = psum(Q, 2), psum(Q, 3), psum(Q, 4), psum(Q, 5)
    q4 = 6*p4 - Pl.polymul(p2, p2)
    r = [p3, q4]
    if mode == 1:
        r.append(p5[5:10])  # s^5..s^9 vanish (s^10 is the leading term)
    return np.concatenate(r)

def jac(f, x, h=1e-7):
    f0 = f(x); J = np.zeros((len(f0), len(x)), dtype=f0.dtype)
    for k in range(len(x)):
        e = np.zeros(len(x), dtype=x.dtype); e[k] = h
        J[:, k] = (f(x+e) - f(x-e))/(2*h)
    return J

def solve(x0, mode, G, g, iters=200, tol=1e-12):
    f = lambda x: np.concatenate([eqs(x, mode), G @ x - g])
    x = x0.copy(); lam = 1e-3
    for it in range(iters):
        F = f(x); nf = np.linalg.norm(F)
        if not np.isfinite(nf): return None, np.inf
        if nf < tol: return x, nf
        J = jac(f, x)
        while True:
            dx = np.linalg.solve(J.T @ J + lam*np.eye(len(x)), -J.T @ F)
            if np.linalg.norm(f(x+dx)) < nf:
                x = x + dx; lam = max(lam/3, 1e-12); break
            lam *= 4
            if lam > 1e8: return x, nf
    return x, np.linalg.norm(f(x))

def diagnostics(x, mode):
    Q = qpolys(x)
    M = Q  # 9 x 3
    sv = np.linalg.svd(M, compute_uv=False)
    nq = np.linalg.norm(Q, axis=1)
    pair = min(min(np.linalg.norm(Q[i]-sg*Q[j]) for sg in (1, -1)) for i in range(n) for j in range(i+1, n))
    J = jac(lambda y: eqs(y, mode), x)
    s = np.linalg.svd(J, compute_uv=False)
    return dict(rank3=sv[-1]/sv[0], minnorm=nq.min()/nq.max(), pair=pair/nq.max(),
                jac_rank=int((s > 1e-8*s[0]).sum()), jac_sv=s[-3:])

if __name__ == '__main__':
    seed, starts, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    out = sys.argv[4] if len(sys.argv) > 4 else f'cy4_m{mode}_s{seed}.npy'
    rs = np.random.RandomState(seed)
    ngauge = 4 if mode == 0 else 2
    good = []
    for st in range(starts):
        G = rs.randn(ngauge, 24); g = np.ones(ngauge)
        x0 = rs.randn(24)
        x, r = solve(x0, mode, G, g)
        if x is None or r > 1e-10: continue
        d = diagnostics(x, mode)
        ok = d['rank3'] > 1e-4 and d['minnorm'] > 1e-4 and d['pair'] > 1e-4
        print(st, f"res={r:.1e} rank3={d['rank3']:.2e} minq={d['minnorm']:.2e} pair={d['pair']:.2e} "
              f"jrank={d['jac_rank']} ok={ok}", flush=True)
        if ok: good.append(x)
    np.save(out, np.array(good))
    print('good', len(good), 'of', starts)
