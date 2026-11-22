#!/usr/bin/env python3
"""Session 59: is L_135 (or another P-dense locus) inside row G's hypersurface Z_G?

Row G (Bezier x P-quartic graph, summary G1a.1): tau is good iff for some (a, b) the
5 x 3 matrix M(a,b) of t^4..t^8 coefficients of X^k mod chi_tau (k = 2, 3, 4),
X = t^3 + a t^2 + b t, has rank <= 2.

For a given tau we solve M(a,b) c = 0 with c = w0 + x1 w1 + x2 w2 (random normalisation),
5 complex equations in 4 unknowns (a, b, x1, x2), by Gauss-Newton from many starts,
and report the smallest relative residual.  tau in Z_G <=> min residual ~ 0.

usage: python3 zg59.py <mode> <npoints> <starts> <seed>
  mode: rand (random complex tau), plant (tau from 9 of the 12 crossings of a random
        Bezier x quartic: control), l135c (random complex point of L_135),
        l135r (random totally real point of L_135), x3 (random complex point of X = {p1=p3=0}),
        vodd (complex point of V_odd = {p1=p3=p5=p7=0})
"""
import sys
import numpy as np

n = 9


def remainder_rows(tau, vals):
    V = np.vander(tau, n, increasing=True)
    return np.linalg.solve(V, vals)  # coefficients 0..8


def Mmat(tau, a, b):
    X = tau**3 + a * tau**2 + b * tau
    cols, da, db = [], [], []
    V = np.vander(tau, n, increasing=True)
    for k in (2, 3, 4):
        vals = np.stack([X**k, k * X**(k - 1) * tau**2, k * X**(k - 1) * tau], axis=1)
        co = np.linalg.solve(V, vals)[4:9]
        cols.append(co[:, 0]); da.append(co[:, 1]); db.append(co[:, 2])
    return np.array(cols).T, np.array(da).T, np.array(db).T


def solve_tau(tau, starts, rng):
    W = rng.normal(size=(3, 3)) + 1j * rng.normal(size=(3, 3))
    best = (np.inf, None)
    for s in range(starts):
        z = (rng.normal(size=4) + 1j * rng.normal(size=4)) * 2.0
        for it in range(int(__import__("os").environ.get("ITER", "80"))):
            a, b, x1, x2 = z
            c = W[0] + x1 * W[1] + x2 * W[2]
            M, Ma, Mb = Mmat(tau, a, b)
            F = M @ c
            J = np.stack([Ma @ c, Mb @ c, M @ W[1], M @ W[2]], axis=1)
            if not np.all(np.isfinite(J)) or not np.all(np.isfinite(F)):
                break
            dz = np.linalg.lstsq(J, -F, rcond=None)[0]
            z = z + dz
            if np.linalg.norm(dz) < 1e-14 * (1 + np.linalg.norm(z)):
                break
        a, b, x1, x2 = z
        c = W[0] + x1 * W[1] + x2 * W[2]
        M, _, _ = Mmat(tau, a, b)
        if not np.all(np.isfinite(M)):
            continue
        res = np.linalg.norm(M @ c) / (np.linalg.norm(M) * np.linalg.norm(c))
        if res < best[0]:
            sv = np.linalg.svd(M, compute_uv=False)
            best = (res, (a, b, sv[-1] / sv[0], sv[-2] / sv[0]))
    return best


def psums(tau, ks):
    return np.array([np.sum(tau**k) for k in ks])


def newton_fix(tau, ks, idx, real=False, it=60):
    for _ in range(it):
        F = psums(tau, ks)
        J = np.array([[k * tau[i]**(k - 1) for i in idx] for k in ks])
        d = np.linalg.solve(J, -F)
        tau = tau.copy(); tau[idx] += d
        if np.linalg.norm(d) < 1e-15:
            break
    return tau


def sample(mode, rng):
    if mode == 'rand':
        t = rng.normal(size=n) + 1j * rng.normal(size=n)
        return t - t.mean()
    if mode == 'plant':
        a, b = rng.normal(size=2)
        Y = rng.normal(size=4); Q = rng.normal(size=5)
        Xp = np.poly1d([1, a, b, 0])
        N = np.poly1d(Y)
        for i in range(5):
            N = N - Q[i] * Xp**(4 - i)
        r = N.roots
        t = r[rng.permutation(12)[:9]]
        return t - t.mean()
    ks = {'l135c': [1, 3, 5], 'l135r': [1, 3, 5], 'x3': [1, 3], 'vodd': [1, 3, 5, 7]}[mode]
    for _ in range(200):
        if mode == 'l135r':
            t = rng.normal(size=n) * 1.5
        else:
            t = rng.normal(size=n) + 1j * rng.normal(size=n)
        idx = list(rng.permutation(n)[:len(ks)])
        try:
            t2 = newton_fix(t, ks, idx)
        except np.linalg.LinAlgError:
            continue
        if np.all(np.isfinite(t2)) and np.max(np.abs(psums(t2, ks))) < 1e-10:
            sep = min(abs(t2[i] - t2[j]) for i in range(n) for j in range(i))
            if sep > 0.05 and np.max(np.abs(t2)) < 20:
                return t2
    raise RuntimeError('no sample')


def main():
    mode, npts, starts, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    rng = np.random.default_rng(seed)
    for p in range(npts):
        tau = sample(mode, rng)
        res, info = solve_tau(tau, starts, rng)
        a, b, s3, s2 = info
        print(f"{mode} pt {p}: min rel residual {res:.2e}  sv3/sv1 {s3:.2e} sv2/sv1 {s2:.2e}  "
              f"|a|,|b| = {abs(a):.3g},{abs(b):.3g}", flush=True)


if __name__ == '__main__':
    main()
