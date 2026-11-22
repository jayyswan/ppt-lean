#!/usr/bin/env python3
"""Session 55: quadrilateral-residual conics in V_3 (n = 9), complex count.

Mechanism: Q a point of V_3 = {p1 = p2 = p3 = 0}, l1 = Q + tau v1 and
l3 = Q + tau v3 two lines of V_3 through Q.  A quadrilateral l1, l3, l2, l4
(l4 through x1 in l1 and Q', l2 through x3 in l3 and Q') spans a P^3 Lam;
S = Lam cap {p2 = 0} contains the four lines (classes 2(1,0) + 2(0,1)), so
S cap {p3 = 0} = quadrilateral + a residual conic C in V_3 (class (1,1)),
on which p4 has degree 8.  The 4th vertices Q' form a curve Sigma; this
script counts its fibre over a generic x1 in l1 (the degree d1 of Sigma -> l1).

Unknowns: v (9), t, sigma.  Q' = x1 + t v, x3 = Q + sigma v3.
Equations: line x1 + tau v in V_3 (3 linear, 2 quadrics, 1 cubic in v),
gauge l(v) = 1, l0(v) = 0, and line x3 Q' in V_3:
  Tr(x3 Q') = Tr(x3^2 Q') = Tr(x3 Q'^2) = 0.
Usage: quad55.py <seed> <starts>
"""
import sys
import numpy as np

n = 9


def rnd(rng, *s):
    return rng.standard_normal(s) + 1j * rng.standard_normal(s)


def newton(F, J, z, it=80, tol=1e-11):
    for _ in range(it):
        f = F(z)
        if not np.all(np.isfinite(f)):
            return None
        if np.linalg.norm(f) < tol:
            return z
        try:
            dz = np.linalg.lstsq(J(z), -f, rcond=None)[0]
        except np.linalg.LinAlgError:
            return None
        lam = 1.0
        nf = np.linalg.norm(f)
        for _ in range(20):
            zn = z + lam * dz
            fn = F(zn)
            if np.all(np.isfinite(fn)) and np.linalg.norm(fn) < nf * (1 - 0.3 * lam) + 1e-300:
                break
            lam *= 0.5
        z = zn
    return z if np.linalg.norm(F(z)) < tol * 100 else None


def point_V3(rng):
    A = rnd(rng, 6, n)  # random slices: y = y0 + A^T c ... use min-norm Newton on p1,p2,p3

    def F(y):
        return np.array([y.sum(), (y ** 2).sum(), (y ** 3).sum()])

    def J(y):
        return np.array([np.ones(n), 2 * y, 3 * y ** 2])
    while True:
        y = newton(F, J, rnd(rng, n))
        if y is not None:
            return y / np.linalg.norm(y)


def line_dir(rng, x):
    """random point on the curve of lines through x in V_3 (direction v)."""
    l0, l1, l2 = rnd(rng, n), rnd(rng, n), rnd(rng, n)

    def F(v):
        return np.array([v.sum(), (x * v).sum(), (x * x * v).sum(), (v * v).sum(),
                         (x * v * v).sum(), (v ** 3).sum(), l0 @ v, l1 @ v - 1, l2 @ v])

    def J(v):
        return np.array([np.ones(n), x, x * x, 2 * v, 2 * x * v, 3 * v * v, l0, l1, l2])
    while True:
        v = newton(F, J, rnd(rng, n))
        if v is not None:
            return v


def setup(seed):
    rng = np.random.default_rng(seed)
    Q = point_V3(rng)
    v1 = line_dir(rng, Q)
    v3 = line_dir(rng, Q)
    a = rnd(rng)[()] if False else complex(rng.standard_normal(), rng.standard_normal())
    x1 = Q + a * v1
    return rng, Q, v1, v3, x1


def system(Q, v1, v3, x1, l0, l1):
    def F(z):
        v, t, s = z[:n], z[n], z[n + 1]
        Qp = x1 + t * v
        x3 = Q + s * v3
        return np.array([v.sum(), (x1 * v).sum(), (x1 * x1 * v).sum(), (v * v).sum(),
                         (x1 * v * v).sum(), (v ** 3).sum(), l0 @ v, l1 @ v - 1,
                         (x3 * Qp).sum(), (x3 * x3 * Qp).sum(), (x3 * Qp * Qp).sum()])

    def J(z):
        v, t, s = z[:n], z[n], z[n + 1]
        Qp = x1 + t * v
        x3 = Q + s * v3
        M = np.zeros((11, n + 2), complex)
        M[0, :n] = 1
        M[1, :n] = x1
        M[2, :n] = x1 * x1
        M[3, :n] = 2 * v
        M[4, :n] = 2 * x1 * v
        M[5, :n] = 3 * v * v
        M[6, :n] = l0
        M[7, :n] = l1
        # dQp/dv = t I, dQp/dt = v ; dx3/ds = v3
        M[8, :n] = t * x3
        M[8, n] = (x3 * v).sum()
        M[8, n + 1] = (v3 * Qp).sum()
        M[9, :n] = t * x3 * x3
        M[9, n] = (x3 * x3 * v).sum()
        M[9, n + 1] = (2 * x3 * v3 * Qp).sum()
        M[10, :n] = 2 * t * x3 * Qp
        M[10, n] = (2 * x3 * Qp * v).sum()
        M[10, n + 1] = (v3 * Qp * Qp).sum()
        return M
    return F, J


def canon(Qp):
    k = np.argmax(np.abs(Qp))
    return Qp / Qp[k]


def check_sol(z, Q, v1, v3, x1, F, J):
    v, t, s = z[:n], z[n], z[n + 1]
    Qp = x1 + t * v
    x3 = Q + s * v3
    # exclusions
    B = np.array([v1, x1]).T
    res = v - B @ np.linalg.lstsq(B, v, rcond=None)[0]
    if np.linalg.norm(res) < 1e-6 * np.linalg.norm(v):
        return None, 'l1'
    if abs(s) < 1e-6:
        return None, 'sig0'
    if abs(t) < 1e-8:
        return None, 't0'
    sv = np.linalg.svd(J(z), compute_uv=False)
    if sv[-1] / sv[0] < 1e-10:
        return None, 'sing'
    return (Qp, x3, v, t, s), 'ok'


def main():
    seed, starts = int(sys.argv[1]), int(sys.argv[2])
    rng, Q, v1, v3, x1 = setup(seed)
    l0, l1 = rnd(rng, n), rnd(rng, n)
    F, J = system(Q, v1, v3, x1, l0, l1)
    sols = []
    rej = {}
    for i in range(starts):
        z0 = np.concatenate([rnd(rng, n), rnd(rng, 2)])
        z = newton(F, J, z0)
        if z is None:
            rej['fail'] = rej.get('fail', 0) + 1
            continue
        r, why = check_sol(z, Q, v1, v3, x1, F, J)
        if r is None:
            rej[why] = rej.get(why, 0) + 1
            continue
        c = canon(r[0])
        if all(np.linalg.norm(c - canon(s[0])) > 1e-6 for s in sols):
            sols.append(r)
        if (i + 1) % 200 == 0:
            print(f'starts {i+1}: distinct {len(sols)}  rejected {rej}', flush=True)
    print(f'FINAL seed {seed}: distinct 4th vertices Q\' = {len(sols)}  rejected {rej}')
    np.save(f'quad55_{seed}.npy', np.array([np.concatenate([s[0], s[1], [s[3], s[4]]]) for s in sols]) if sols else np.zeros(0))


if __name__ == '__main__':
    main()
