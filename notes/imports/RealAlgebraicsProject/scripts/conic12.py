# conic12.py  (session 46)
# Conics in V_3 = {p1 = p2 = p3 = 0} through two points Q1, Q2 of V_3.
# Parametrise q(k) = Q1 + k u + k^2 Q2.  Linear conditions put u in the
# 4-dim space L = {Tr(e u) = 0, e in 1, Q1, Q2, Q1^2, Q2^2}; the rest is
#   Tr(u^2) = -2m, Tr(Q1 u^2) = -a, Tr(Q2 u^2) = -b, Tr(u^3) + 6 Tr(Q1 Q2 u) = 0,
# m = Tr(Q1 Q2), a = Tr(Q1^2 Q2), b = Tr(Q1 Q2^2).  Writing u = U / t, s = t^2,
# and eliminating s = -Tr(U^2)/(2m): the conics are the points of
#   E  = {a A1 - 2m A2 = 0, b A1 - 2m A4 = 0}   (genus-one quartic curve in P(L) = P^3)
#   S3 = {m Tr(U^3) - 3 Tr(Q1 Q2 U) Tr(U^2) = 0}   (cubic surface)
# with A1 = Tr(U^2), A2 = Tr(Q1 U^2), A4 = Tr(Q2 U^2): 12 points, so N = 12.
# Usage: python3 conic12.py <r> <pairs> <seed>     (real Q1, Q2 in R^r x C^s)
#        python3 conic12.py c <pairs> <seed>       (complex generic Q1, Q2)
import numpy as np, sys

def realmap(r):
    M = np.zeros((9, 9), complex)
    for i in range(r): M[i, i] = 1
    for j in range((9 - r) // 2):
        a = r + 2 * j
        M[a, a] = 1; M[a, a + 1] = 1j; M[a + 1, a] = 1; M[a + 1, a + 1] = -1j
    return M

def psums(y, ks=(1, 2, 3)):
    return np.array([np.sum(y ** k) for k in ks])

def v3_point(rng, r=None, tol=1e-13):
    """random point of V_3: real (signature r) if r is an int, complex if r is None"""
    M = realmap(r) if r is not None else np.eye(9)
    for _ in range(50):
        w = rng.normal(size=9) if r is not None else rng.normal(size=9) + 1j * rng.normal(size=9)
        w /= np.linalg.norm(w)
        for it in range(60):
            y = M @ w
            F = psums(y)
            J = np.array([k * y ** (k - 1) for k in (1, 2, 3)]) @ M
            if r is not None: F, J = F.real, J.real
            if np.linalg.norm(F) < tol: break
            w = w - np.linalg.pinv(J) @ F
        if np.linalg.norm(F) < tol and np.all(np.isfinite(w)):
            w /= np.linalg.norm(w)
            y = M @ w
            # polish once more after normalising (cone, so still on V_3)
            return y
    raise RuntimeError('no V3 point')

def setup(Q1, Q2, r=None):
    E = np.array([np.ones(9), Q1, Q2, Q1 ** 2, Q2 ** 2])
    if r is not None:
        M = realmap(r)
        Fm = (E @ M).real
        _, sv, Vh = np.linalg.svd(Fm)
        N = Vh[5:].T
        Lb = M @ N
    else:
        _, sv, Vh = np.linalg.svd(E)
        Lb = Vh[5:].conj().T
    m = np.sum(Q1 * Q2); a = np.sum(Q1 ** 2 * Q2); b = np.sum(Q1 * Q2 ** 2)
    S = {k: Lb.T @ np.diag(e) @ Lb for k, e in (('1', np.ones(9)), ('Q1', Q1), ('Q2', Q2))}
    lv = Lb.T @ (Q1 * Q2)
    return dict(Q1=Q1, Q2=Q2, Lb=Lb, m=m, a=a, b=b, S=S, lv=lv, r=r)

def fsys(D, c):
    S = D['S']; m, a, b = D['m'], D['a'], D['b']
    A1 = c @ S['1'] @ c; A2 = c @ S['Q1'] @ c; A4 = c @ S['Q2'] @ c
    y = D['Lb'] @ c
    C3 = np.sum(y ** 3); l = D['lv'] @ c
    F = np.array([a * A1 - 2 * m * A2, b * A1 - 2 * m * A4, m * C3 - 3 * l * A1])
    g1 = 2 * S['1'] @ c; g2 = 2 * S['Q1'] @ c; g4 = 2 * S['Q2'] @ c
    gC = 3 * D['Lb'].T @ (y ** 2)
    J = np.array([a * g1 - 2 * m * g2, b * g1 - 2 * m * g4, m * gC - 3 * (l * g1 + A1 * D['lv'])])
    return F, J

def solve12(D, rng, steps_min=1e-6):
    """total-degree homotopy (degrees 2, 2, 3) in a random affine chart of P^3"""
    B = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
    gam = np.exp(2j * np.pi * rng.random())
    deg = np.array([2, 2, 3])
    def H(x, t):
        c = B @ np.concatenate([[1], x])
        F, J = fsys(D, c)
        Jx = J @ B[:, 1:]
        g = x ** deg - 1
        Jg = np.diag(deg * x ** (deg - 1))
        return (1 - t) * gam * g + t * F, (1 - t) * gam * Jg + t * Jx, F - gam * g
    starts = []
    for e1 in (1, -1):
        for e2 in (1, -1):
            for k in range(3):
                starts.append(np.array([e1, e2, np.exp(2j * np.pi * k / 3)], complex))
    ends = []
    for x in starts:
        t = 0.0; h = 0.01; ok = True
        while t < 1:
            h = min(h, 1 - t)
            _, Jh, Ht = H(x, t)
            try: dx = -np.linalg.solve(Jh, Ht)
            except np.linalg.LinAlgError: ok = False; break
            xp = x + h * dx; tn = t + h
            conv = False
            for it in range(6):
                Hv, Jh, _ = H(xp, tn)
                try: d = np.linalg.solve(Jh, Hv)
                except np.linalg.LinAlgError: break
                xp = xp - d
                if np.linalg.norm(d) < 1e-10 * (1 + np.linalg.norm(xp)): conv = True; break
                if it == 1 and np.linalg.norm(d) > 0.1 * (1 + np.linalg.norm(xp)): break
            if conv and np.all(np.isfinite(xp)):
                x, t = xp, tn; h = min(h * 1.5, 0.05)
            else:
                h /= 2
                if h < steps_min: ok = False; break
        c = B @ np.concatenate([[1], x])
        # polish on the target
        b0 = np.linalg.inv(B)[0]
        for it in range(8):
            F, J = fsys(D, c)
            Jc = np.vstack([J, b0[None, :]])
            Fc = np.concatenate([F, [b0 @ c - 1]])
            try: c = c - np.linalg.solve(Jc, Fc)
            except np.linalg.LinAlgError: break
        ends.append((ok, c / np.linalg.norm(c)))
    return ends

def solve_all(D, rng, tries=5):
    sols = []
    for _ in range(tries):
        ends = solve12(D, rng)
        good = [c for ok, c in ends if np.all(np.isfinite(c)) and np.linalg.norm(fsys(D, c)[0]) < 1e-9]
        sols = distinct(sols + good)
        if len(sols) >= 12: break
    return sols

def distinct(cs, tol=1e-6):
    out = []
    for c in cs:
        if all(min(np.linalg.norm(c - d * (d.conj() @ c)), 10) > tol for d in out):
            out.append(c)
    return out

def conic_from(D, c):
    A1 = c @ D['S']['1'] @ c
    s = -A1 / (2 * D['m'])
    U = D['Lb'] @ c
    u = U / np.sqrt(s)
    return u, s

def conic_check(D, u, rng):
    worst = 0
    for kap in rng.normal(size=4) + 1j * rng.normal(size=4):
        q = D['Q1'] + kap * u + kap ** 2 * D['Q2']
        worst = max(worst, np.max(np.abs(psums(q))) / np.linalg.norm(q) ** 3)
    return worst

def p4_poly(D, u):
    P = np.polynomial.polynomial
    tot = np.zeros(9, complex)
    for i in range(9):
        qi = np.array([D['Q1'][i], u[i], D['Q2'][i]])
        tot += P.polypow(qi, 4)
    return tot  # ascending coefficients in kappa

def realroots_p4(D, u):
    co = p4_poly(D, u).real
    rts = np.roots(co[::-1])
    nreal = int(np.sum(np.abs(rts.imag) < 1e-7 * (1 + np.abs(rts))))
    th = np.linspace(-np.pi / 2, np.pi / 2, 4001)[1:-1]
    k = np.tan(th)
    vals = []
    for kap in k:
        q = D['Q1'] + kap * u + kap ** 2 * D['Q2']
        vals.append(np.sum(q ** 4).real / np.linalg.norm(q) ** 4)
    vq2 = np.sum(D['Q2'] ** 4).real / np.linalg.norm(D['Q2']) ** 4
    return nreal, min(min(vals), vq2)

def ratio_classes(D, u, tol=1e-6):
    V = np.array([D['Q1'], u, D['Q2']]).T  # 9 x 3, coordinate forms
    cls = []
    for row in V:
        if np.linalg.norm(row) < tol: key = 'zero'
        else: key = row / row[np.argmax(np.abs(row))]
        if not any((isinstance(k, str) and isinstance(key, str)) or
                   (not isinstance(k, str) and not isinstance(key, str) and np.linalg.norm(k - key) < tol)
                   for k in cls):
            cls.append(key)
    return len(cls)

def main():
    mode = sys.argv[1]; npairs = int(sys.argv[2]); seed = int(sys.argv[3])
    rng = np.random.default_rng(seed)
    r = None if mode == 'c' else int(mode)
    tally = {}
    for pi in range(npairs):
        Q1 = v3_point(rng, r); Q2 = v3_point(rng, r)
        D = setup(Q1, Q2, r)
        dc = solve_all(D, rng)
        info = []
        nreal = 0
        for c in dc:
            u, s = conic_from(D, c)
            chk = conic_check(D, u, rng)
            if r is not None:
                cn = c / c[np.argmax(np.abs(c))]
                isreal = np.max(np.abs(cn.imag)) < 1e-8
                A1 = (cn @ D['S']['1'] @ cn).real
                sr = -A1 / (2 * D['m'].real)
                if isreal and sr > 0:
                    nreal += 1
                    ur = (D['Lb'] @ cn).real / np.sqrt(sr)
                    ur = D['Lb'] @ cn / np.sqrt(sr)
                    nr, mn = realroots_p4(D, ur)
                    rc = ratio_classes(D, ur)
                    info.append((nr, round(mn, 4), rc))
            else:
                info.append(f'{chk:.1e}')
        if r is None:
            print(f'pair {pi}: distinct sols {len(dc)}, conic residuals {info}')
        else:
            sig = '(1,2)' if D['m'].real > 0 else '(2,1)'
            print(f'pair {pi}: m={D["m"].real:+.3f} sig {sig}  distinct {len(dc)}/12  real conics {nreal}: (p4 real roots, min p4/|y|^4, ratio classes) {info}')
            key = (sig, nreal, sum(1 for x in info if x[0] > 0))
            tally[key] = tally.get(key, 0) + 1
    if r is not None:
        print('tally (signature, #real conics, #with real p4 roots):', sorted(tally.items()))

if __name__ == '__main__':
    main()
