#!/usr/bin/env python3
"""Session 53: counts for the surface S_Q of conics through a point Q of
V_S = {p_d = 0, d in S} (default S = 1,2,4), n = 9, generic complex coordinates
(Tr = plain sum).  A conic through Q is q = Q + k u + k^2 w; gauge l0(u) = 0,
l1(u) = 1; equations: coefficients k^1..k^{2d} of p_d(q) for d in S.  For S = 1,2,4
the conics through Q form a surface; it is sliced by two extra equations:
  mode lin2 : l2(u) = l3(u) = 0 (l2, l3 vanish on Q)  -> degree of the tangent map
              S_Q -> P^4 composed with a generic linear projection to P^2
  mode tq2  : Tr(u^2) = 0 and l2(u) = 0 (conics in the tangent hyperplane of {p2=0}
              at Q, cut by one linear condition)
  mode tq4  : Tr(Q^2 u^2) = 0 and l2(u) = 0 (tangent hyperplane of {p4 = 0})
  mode both : Tr(u^2) = 0 and Tr(Q^2 u^2) = 0
Random-start complex Newton; prints the number of distinct nondegenerate solutions
every 200 starts.
usage: c124count.py <mode> <seed> <starts> [S=1,2,4]
"""
import sys, numpy as np

n = 9

def coeff_tab(d):
    N = 2 * d + 1
    k = np.exp(2j * np.pi * np.arange(N) / N) * 0.9
    W = np.linalg.inv(np.vander(k, N, increasing=True))
    return k, W

TABS = {}

def pcoef(Q, u, w, d):
    if d not in TABS: TABS[d] = coeff_tab(d)
    k, W = TABS[d]
    q = Q[None, :] + k[:, None] * u[None, :] + (k ** 2)[:, None] * w[None, :]
    val = (q ** d).sum(1)
    der = d * q ** (d - 1)
    c = W @ val
    Ju = W @ (der * k[:, None]); Jw = W @ (der * (k ** 2)[:, None])
    return c[1:], Ju[1:], Jw[1:]

def point_on_V(S, rng):
    """complex point of V_S by Newton with random affine slices"""
    for _ in range(100):
        L = rng.standard_normal((n - len(S), n)) + 1j * rng.standard_normal((n - len(S), n))
        b = np.zeros(n - len(S), complex); b[0] = 1
        x = rng.standard_normal(n) + 1j * rng.standard_normal(n)
        for it in range(100):
            F = np.concatenate([[np.sum(x ** d) for d in S], L @ x - b])
            J = np.vstack([np.array([d * x ** (d - 1) for d in S]), L])
            dx = np.linalg.solve(J, F); x = x - dx
            if np.linalg.norm(dx) < 1e-14 * (1 + np.linalg.norm(x)): break
        F = np.concatenate([[np.sum(x ** d) for d in S], L @ x - b])
        if np.linalg.norm(F) < 1e-11 and np.isfinite(x).all():
            return x
    raise RuntimeError('no point')

def system(Q, S, mode, rng):
    l = [rng.standard_normal(n) + 1j * rng.standard_normal(n) for _ in range(4)]
    for j in (2, 3):   # make l2, l3 vanish on Q
        l[j] = l[j] - (l[j] @ Q) / (Q @ Q.conj()) * Q.conj()
    Q2 = Q ** 2
    def F(z):
        u, w = z[:n], z[n:]
        out, Ju, Jw = [], [], []
        for d in S:
            c, a, b = pcoef(Q, u, w, d)
            out.append(c); Ju.append(a); Jw.append(b)
        g = [l[0] @ u, l[1] @ u - 1]
        gu = [l[0], l[1]]
        if mode == 'lin2':
            g += [l[2] @ u, l[3] @ u]; gu += [l[2], l[3]]
        elif mode == 'tq2':
            g += [np.sum(u * u), l[2] @ u]; gu += [2 * u, l[2]]
        elif mode == 'tq4':
            g += [np.sum(Q2 * u * u), l[2] @ u]; gu += [2 * Q2 * u, l[2]]
        elif mode == 'both':
            g += [np.sum(u * u), np.sum(Q2 * u * u)]; gu += [2 * u, 2 * Q2 * u]
        out.append(np.array(g)); Ju.append(np.array(gu)); Jw.append(np.zeros((len(g), n)))
        return np.concatenate(out), np.hstack([np.vstack(Ju), np.vstack(Jw)])
    return F

def newton(F, z, it=80):
    for _ in range(it):
        f, J = F(z)
        try:
            dz = np.linalg.solve(J, f)
        except np.linalg.LinAlgError:
            return None
        z = z - dz
        if not np.isfinite(z).all(): return None
        if np.linalg.norm(dz) < 1e-13 * (1 + np.linalg.norm(z)):
            f, J = F(z)
            if np.linalg.norm(f) < 1e-9 * (1 + np.linalg.norm(z)) ** 8:
                return z
            return None
    return None

def main():
    mode = sys.argv[1]; seed = int(sys.argv[2]); starts = int(sys.argv[3])
    S = [int(t) for t in sys.argv[4].split(',')] if len(sys.argv) > 4 else [1, 2, 4]
    rng = np.random.default_rng(seed)
    Q = point_on_V(S, rng)
    F = system(Q, S, mode, rng)
    f0, J0 = F(np.zeros(2 * n, complex) + 0.1)
    assert J0.shape[0] == J0.shape[1], J0.shape
    sols = []
    ndeg = 0
    for st in range(1, starts + 1):
        z0 = (rng.standard_normal(2 * n) + 1j * rng.standard_normal(2 * n)) * rng.choice([0.3, 1, 3])
        z = newton(F, z0)
        if z is not None:
            u, w = z[:n], z[n:]
            R = np.vstack([Q, u, w])
            sv = np.linalg.svd(R, compute_uv=False)
            if sv[2] / sv[0] < 1e-7:
                ndeg += 1
            elif not any(np.linalg.norm(z - s) < 1e-6 * (1 + np.linalg.norm(s)) for s in sols):
                sols.append(z)
        if st % 200 == 0:
            print(f'starts {st}: distinct nondegenerate {len(sols)}, degenerate hits {ndeg}', flush=True)
    np.save(f'c124_{mode}_{seed}.npy', np.array(sols))

if __name__ == '__main__':
    main()
