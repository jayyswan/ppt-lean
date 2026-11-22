# Session 61: row E3 = general cubic Bezier (X(t), Y(t)) x graph y = S(x), S = T_6 fixed rational, all dials in P.
# u in K is good iff S(X(u)) lies in span(1, u, u^2, u^3) for some cubic X (5 conditions, 4 unknowns: a hypersurface).
# Membership test by overdetermined complex Gauss-Newton in x = (x0, x1, x2, x3), many random starts.
# Usage: python3 e3num.py <mode> <npoints> <starts> <seed>
#   plant : 9 of the 18 crossings of a random cubic Bezier with the T_6 graph (positive control)
#   rand  : random complex u (negative control)
#   G     : u = 9 of the 12 crossings of a random row-E member with a random sextic V (u in G, J(u) arbitrary)
#   l135  : random complex point of L_135 (p1 = p3 = p5 = 0)
#   real  : real-root census of T_6(X(t)) - Y(t) for random real cubics (the r = 9 real test)
# Prints per point the smallest relative residual, and |(x1,x2,x3)| at the minimiser (trivial X = const excluded).
import sys, numpy as np
mode, npts, starts, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rng = np.random.default_rng(seed)
T6 = np.polynomial.Polynomial(np.polynomial.chebyshev.cheb2poly([0]*6 + [1]))
dT6 = T6.deriv()
import os
SPREAD = float(os.environ.get("SPREAD", "0.3"))

def resid(x, u, B):
    X = x[0] + x[1]*u + x[2]*u**2 + x[3]*u**3
    f = T6(X)
    r = f - B @ (np.linalg.pinv(B) @ f)
    return r, X

def solve(u):
    B = np.vander(u, 4, increasing=True)
    Q, _ = np.linalg.qr(B)
    P = np.eye(9) - Q @ Q.conj().T          # projector onto the complement of span(1,u,u^2,u^3)
    sc = np.max(np.abs(u)) + 1
    best = (np.inf, None)
    for s in range(starts):
        x = (rng.standard_normal(4) + 1j*rng.standard_normal(4)) * np.array([1, 1/sc, 1/sc**2, 1/sc**3])
        lam = 1e-3
        for it in range(200):
            X = x[0] + x[1]*u + x[2]*u**2 + x[3]*u**3
            f = T6(X); r = P @ f
            J = P @ (dT6(X)[:, None] * np.vander(u, 4, increasing=True))
            # damped Gauss-Newton
            A = J.conj().T @ J; g = J.conj().T @ r
            dx = np.linalg.solve(A + lam*np.diag(np.diag(A).real + 1e-30), -g)
            xn = x + dx
            Xn = xn[0] + xn[1]*u + xn[2]*u**2 + xn[3]*u**3
            if np.linalg.norm(P @ T6(Xn)) < np.linalg.norm(r):
                x = xn; lam = max(lam/3, 1e-12)
            else:
                lam *= 5
                if lam > 1e8: break
        X = x[0] + x[1]*u + x[2]*u**2 + x[3]*u**3
        f = T6(X); r = P @ f
        var = np.linalg.norm(f - f.mean())
        nonconst = np.linalg.norm(X - X.mean())
        if nonconst < SPREAD:   # X nearly constant on u: trivial or the D_K degeneration at an inflection point of S
            continue
        rel = np.linalg.norm(r) / (var + 1e-300)
        if rel < best[0]: best = (rel, x, nonconst)
    return best

def l135_point():
    # Newton for p1 = p3 = p5 = 0 from a random complex start, 3 coordinates solved
    for _ in range(100):
        u = rng.standard_normal(9) + 1j*rng.standard_normal(9)
        for it in range(60):
            F = np.array([u.sum(), (u**3).sum(), (u**5).sum()])
            J = np.vstack([np.ones(9), 3*u**2, 5*u**4])
            du = -np.linalg.pinv(J) @ F
            u = u + du
            if np.linalg.norm(F) < 1e-14: break
        if np.linalg.norm([u.sum(), (u**3).sum(), (u**5).sum()]) < 1e-12 and np.min(np.abs(u[:, None] - u[None, :]) + np.eye(9)) > 1e-3:
            return u
    raise RuntimeError

if mode == 'real':
    from collections import Counter
    cnt = Counter()
    for k in range(npts):
        # X ranging over [-1,1] about three times: X = A*(T_3(t) scaled) + noise
        X = np.polynomial.Polynomial(np.polynomial.chebyshev.cheb2poly([0, 0, 0, 1])) * (1 + 0.05*rng.standard_normal()) \
            + np.polynomial.Polynomial(0.05*rng.standard_normal(4))
        Y = np.polynomial.Polynomial(0.3*rng.standard_normal(4))
        N = T6(X) - Y
        rts = N.roots()
        cnt[int(np.sum(np.abs(rts.imag) < 1e-9))] += 1
    print('real-root counts of T6(X(t)) - Y(t), degree 18:', dict(sorted(cnt.items())))
    sys.exit()

for k in range(npts):
    if mode == 'plant':
        X = np.polynomial.Polynomial(rng.standard_normal(4))
        Y = np.polynomial.Polynomial(rng.standard_normal(4))
        rts = (T6(X) - Y).roots()
        u = rts[rng.permutation(18)[:9]]
    elif mode == 'rand':
        u = rng.standard_normal(9) + 1j*rng.standard_normal(9)
    elif mode == 'G':
        V = np.polynomial.Polynomial(np.r_[rng.standard_normal(6), 1])
        al, be = rng.standard_normal(2)
        Y = np.polynomial.Polynomial(rng.standard_normal(4))
        rts = (V(np.polynomial.Polynomial([be, 0, al])) - Y).roots()
        u = rts[rng.permutation(12)[:9]]
    elif mode == 'l135':
        u = l135_point()
    rel, x, nc = solve(u)
    print(f'{mode} {k}: min relative residual {rel:.2e}   |X - mean| on u {nc:.2e}   x = {np.round(x, 3) if x is not None else None}')
