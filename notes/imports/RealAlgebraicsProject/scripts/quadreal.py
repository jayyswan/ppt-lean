#!/usr/bin/env python3
"""Session 55: real test for quadrilateral-residual conics in V_3 (n = 9).

K (x) R = R^r x C^s modelled in C^9 (coords r real, then s conjugate pairs).
For a random real point Q of V_3, two real lines l1, l3 of V_3 through Q
(real points of the curve C_Q) and a real x1 on l1, all complex solutions
(Q', sigma) of quad55's system are found by random starts; the real ones give
real quadrilaterals, their residual conic C (class (1,1) on S), its plane
signature, and the number of sign changes of p4 along the real conic.
Usage: quadreal.py <r> <trials> <seed> [starts=1500]
"""
import sys
import numpy as np
exec(open('quad55.py').read().split("\ndef main")[0])

r = int(sys.argv[1]); trials = int(sys.argv[2]); seed = int(sys.argv[3])
starts = int(sys.argv[4]) if len(sys.argv) > 4 else 1500
s_ = (n - r) // 2
M = np.zeros((n, n), complex)
for i in range(r):
    M[i, i] = 1
for k in range(s_):
    a, b = r + 2 * k, r + 2 * k + 1
    M[a, a] = 1; M[a, b] = 1j
    M[b, a] = 1; M[b, b] = -1j
Minv = np.linalg.inv(M)


def realpart(y):  # real coordinates of a (projectively) real vector, or None
    u = Minv @ y
    k = np.argmax(np.abs(u))
    u = u / u[k]
    if np.linalg.norm(u.imag) > 1e-7:
        return None
    return u.real


def rnewton(F, J, u, it=100):
    for _ in range(it):
        f = F(u)
        if not np.all(np.isfinite(f)):
            return None
        if np.linalg.norm(f) < 1e-12:
            return u
        du = np.linalg.lstsq(J(u), -f, rcond=None)[0]
        u = u + du
    return u if np.linalg.norm(F(u)) < 1e-9 else None


def real_V3(rng):
    def F(u):
        y = M @ u
        return np.array([(y ** k).sum().real for k in (1, 2, 3)])

    def J(u):
        y = M @ u
        return np.array([((k * y ** (k - 1)) @ M).real for k in (1, 2, 3)])
    while True:
        u = rnewton(F, J, rng.standard_normal(n))
        if u is not None:
            y = M @ u
            if min(abs(y[i] - y[j]) for i in range(n) for j in range(i)) > 1e-3:
                return y / np.linalg.norm(y)


def real_line_dir(rng, x, tries=200):
    for _ in range(tries):
        L0, L1 = rng.standard_normal(n), rng.standard_normal(n)

        def F(u):
            v = M @ u
            e = [v.sum(), (x * v).sum(), (x * x * v).sum(), (v * v).sum(), (x * v * v).sum(), (v ** 3).sum()]
            return np.concatenate([np.array(e).real, [L0 @ u, L1 @ u - 1]])

        def J(u):
            v = M @ u
            rows = [np.ones(n), x, x * x, 2 * v, 2 * x * v, 3 * v * v]
            return np.vstack([np.array([(rw @ M) for rw in rows]).real, L0, L1])
        u = rnewton(F, J, rng.standard_normal(n))
        if u is not None:
            return M @ u
    return None


def conic_data(Q, x1, x3, Qp):
    B = np.array([Q, x1, x3, Qp]).T
    rs = np.random.default_rng(7).standard_normal((60, 4))
    Y = rs @ B.T
    p2 = (Y ** 2).sum(1); p3 = (Y ** 3).sum(1)
    A = np.hstack([(rs[:, 3] * rs[:, 0])[:, None] * rs, p2[:, None] * rs])
    sol = np.linalg.lstsq(A, p3, rcond=None)[0]
    res = np.linalg.norm(A @ sol - p3) / np.linalg.norm(p3)
    hC = sol[:4]
    k = np.argmax(np.abs(hC)); hC = hC / hC[k]
    hC = hC.real
    Nb = np.linalg.svd(hC[None, :])[2][1:]
    P = Nb @ B.T  # 3 x 9 complex (real structure via M)
    G = (P @ P.T).real
    w, V = np.linalg.eigh(G)
    sig = (int((w > 0).sum()), int((w < 0).sum()))
    if sig not in [(2, 1), (1, 2)]:
        return res, sig, None, None
    if sig == (1, 2):
        w = -w
    ip = [i for i in range(3) if w[i] > 0]; ineg = [i for i in range(3) if w[i] < 0][0]
    th = np.linspace(0, 2 * np.pi, 4001)[:-1]
    co = (np.outer(np.cos(th), V[:, ip[0]]) / np.sqrt(w[ip[0]]) +
          np.outer(np.sin(th), V[:, ip[1]]) / np.sqrt(w[ip[1]]) +
          V[:, ineg][None, :] / np.sqrt(-w[ineg]))
    Y = co @ P
    Y = Y / np.linalg.norm(Y, axis=1)[:, None]
    chk = max(np.abs((Y ** k).sum(1)).max() for k in (1, 2, 3))
    p4 = (Y ** 4).sum(1).real
    ch = int((np.diff(np.sign(np.concatenate([p4, p4[:1]]))) != 0).sum())
    return res, sig, ch, (chk, p4.min(), p4.max())


def main():
    rng = np.random.default_rng(seed)
    tally = {}
    for T in range(trials):
        Q = real_V3(rng)
        v1 = real_line_dir(rng, Q); v3 = real_line_dir(rng, Q)
        if v1 is None or v3 is None:
            print('trial', T, 'no real lines through Q'); continue
        a = rng.standard_normal()
        x1 = Q + a * v1
        l0, l1 = rnd(rng, n), rnd(rng, n)
        F, J = system(Q, v1, v3, x1, l0, l1)
        sols = []
        for i in range(starts):
            z = newton(F, J, np.concatenate([rnd(rng, n), rnd(rng, 2)]))
            if z is None:
                continue
            rr, why = check_sol(z, Q, v1, v3, x1, F, J)
            if rr is None:
                continue
            c = canon(rr[0])
            if all(np.linalg.norm(c - canon(sx[0])) > 1e-6 for sx in sols):
                sols.append(rr)
        nreal = 0; info = []
        for (Qp, x3, v, t, sg) in sols:
            ur = realpart(Qp)
            if ur is None or abs(sg.imag) > 1e-7:
                continue
            nreal += 1
            Qr = M @ ur
            res, sig, ch, ex = conic_data(Q, x1, x3, Qr)
            info.append((sig, ch))
            key = (sig, ch)
            tally[key] = tally.get(key, 0) + 1
        print(f'trial {T}: complex {len(sols)}, real {nreal}, (plane sig, p4 sign changes): {info}', flush=True)
    print('TALLY r =', r, tally)


if __name__ == '__main__':
    main()
