# mono12.py  (session 46)  numerical monodromy of the 12 conics through Q1, Q2 in V_3
# as Q2 moves on loops in V_3 (Q1 fixed, complex generic).  Tracks the 24 vectors u
# (q = Q1 + k u + k^2 Q2, the conic is {u, -u}).
# Usage: python3 mono12.py <seed> <loops> [R]   (writes mono12_<seed>.pkl)
import numpy as np, sys, pickle
exec(open('conic12.py').read().split("\nif __name__ == '__main__'")[0])

def usys(Q1, Q2, u):
    F = np.array([np.sum(u), np.sum(Q1 * u), np.sum(u * u) + 2 * np.sum(Q1 * Q2), np.sum(u * Q2),
                  np.sum(Q1 ** 2 * u), np.sum(Q1 * u * u) + np.sum(Q1 ** 2 * Q2),
                  np.sum(u ** 3) + 6 * np.sum(Q1 * u * Q2), np.sum(u * u * Q2) + np.sum(Q1 * Q2 ** 2),
                  np.sum(u * Q2 ** 2)])
    J = np.array([np.ones(9), Q1, 2 * u, Q2, Q1 ** 2, 2 * Q1 * u, 3 * u * u + 6 * Q1 * Q2, 2 * u * Q2, Q2 ** 2])
    return F, J

def newton_u(Q1, Q2, u, its=8):
    for it in range(its):
        F, J = usys(Q1, Q2, u)
        try: d = np.linalg.solve(J, F)
        except np.linalg.LinAlgError: return u, False
        u = u - d
        if np.linalg.norm(d) < 1e-12 * (1 + np.linalg.norm(u)): return u, True
    return u, np.linalg.norm(usys(Q1, Q2, u)[0]) < 1e-9

def q2_on_path(Z, Dm, c):
    for it in range(20):
        y = Z + Dm @ c
        F = psums(y)
        J = np.array([k * y ** (k - 1) for k in (1, 2, 3)]) @ Dm
        d = np.linalg.solve(J, F)
        c = c - d
        if np.linalg.norm(d) < 1e-14: break
    return c, Z + Dm @ c

def loop(Q1, Q20, us0, d, R, Dm, nsteps=600):
    us = [u.copy() for u in us0]
    c = np.zeros(3, complex)
    th = 0.0; h = 2 * np.pi / nsteps
    Q2prev = Q20
    while th < 2 * np.pi - 1e-15:
        h = min(h, 2 * np.pi - th)
        tn = th + h
        Z = Q20 + R * (np.exp(1j * tn) - 1) * d
        cn, Q2n = q2_on_path(Z, Dm, c)
        if not np.all(np.isfinite(Q2n)) or np.linalg.norm(Q2n - Q2prev) > 0.05:
            h /= 2
            if h < 1e-7: return None
            continue
        new = []; ok = True
        for u in us:
            un, conv = newton_u(Q1, Q2n, u)
            if not conv or np.linalg.norm(un - u) > 0.1 * (1 + np.linalg.norm(u)): ok = False; break
            new.append(un)
        if ok:
            A = np.array(new)
            dmin = min(np.linalg.norm(A[i] - A[j]) for i in range(24) for j in range(i))
            if dmin < 1e-4: ok = False
        if not ok:
            h /= 2
            if h < 1e-7: return None
            continue
        us, c, th, Q2prev = new, cn, tn, Q2n
        h = min(h * 1.3, 2 * np.pi / nsteps)
    return us, c

def main():
    seed = int(sys.argv[1]); nloops = int(sys.argv[2]); Rs = float(sys.argv[3]) if len(sys.argv) > 3 else 0.5
    rng = np.random.default_rng(seed)
    Q1 = v3_point(rng); Q20 = v3_point(rng)
    D = setup(Q1, Q20)
    cs = solve_all(D, rng)
    assert len(cs) == 12, len(cs)
    us0 = []
    for c in cs:
        u, s = conic_from(D, c)
        u, ok = newton_u(Q1, Q20, u); assert ok
        us0 += [u, -u]
    perms = []
    for li in range(nloops):
        d = rng.normal(size=9) + 1j * rng.normal(size=9); d /= np.linalg.norm(d)
        Dm = rng.normal(size=(9, 3)) + 1j * rng.normal(size=(9, 3))
        R = Rs * (0.5 + rng.random())
        res = loop(Q1, Q20, us0, d, R, Dm)
        if res is None: print(f'loop {li}: failed'); continue
        us1, c1 = res
        if np.linalg.norm(c1) > 1e-8:
            print(f'loop {li}: Q2 did not return (|c| = {np.linalg.norm(c1):.2e}), skipped'); continue
        p = []
        for u in us1:
            dists = [np.linalg.norm(u - v) for v in us0]
            j = int(np.argmin(dists))
            if dists[j] > 1e-6: p = None; break
            p.append(j)
        if p is None or len(set(p)) != 24: print(f'loop {li}: matching failed'); continue
        # induced permutation on the 12 conics {2i, 2i+1}
        P12 = [p[2 * i] // 2 for i in range(12)]
        consistent = all(p[2 * i + 1] // 2 == P12[i] for i in range(12))
        # cycle type
        seen = set(); ct = []
        for i in range(12):
            if i in seen: continue
            k = i; L = 0
            while k not in seen: seen.add(k); k = P12[k]; L += 1
            ct.append(L)
        print(f'loop {li}: R={R:.2f} cycle type {sorted(ct, reverse=True)} consistent={consistent}', flush=True)
        perms.append((p, P12))
    pickle.dump(dict(Q1=Q1, Q20=Q20, us0=us0, perms=perms), open(f'mono12_{seed}.pkl', 'wb'))
    try:
        from sympy.combinatorics import Permutation, PermutationGroup
        from math import factorial
        G = PermutationGroup([Permutation(P12) for _, P12 in perms if P12 != list(range(12))])
        print('group on 12 conics: order', G.order(), 'transitive', G.is_transitive(),
              'primitive', G.is_primitive() if G.is_transitive() else None, 'S12' if G.order() == factorial(12) else '')
        G24 = PermutationGroup([Permutation(p) for p, _ in perms if p != list(range(24))])
        print('group on 24 vectors u: order', G24.order())
    except Exception as e:
        print('sympy step failed:', e)

if __name__ == '__main__':
    main()
