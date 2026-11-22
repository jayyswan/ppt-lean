# deg47.py  (session 47)
# Degenerations of the two-point slice of S46.1 (conics in V_3 through Q1, Q2).
# The 12 conics are E ∩ S3 in P(L) = P^3, E the base curve of the pencil
#   Tr(rho U^2)|_L,  rho = l1 (a - 2m Q1) + l2 (b - 2m Q2).
# Mode 'line': real points Q2 of R' (E contains a line), Q1 fixed; the line meets S3
#   in 3 points (a cubic step); reports the real ones, s = -Tr(U^2)/(2m), p4 real roots.
# Mode 'rank2': real points Q2 of R (pencil has a rank-2 member); reports the
#   signature of the rank-2 form (real planes iff (1,1)), the two conics, their
#   6 points on S3, real ones with s > 0 and p4 real roots.
# Both: the discriminant quartic det(pencil) and its root pattern (Segre check).
# Usage: python3 deg47.py <line|rank2> <r> <starts> <seed>
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

def v3_point(rng, M, tol=1e-13):
    for _ in range(50):
        w = rng.normal(size=9); w /= np.linalg.norm(w)
        for it in range(60):
            y = M @ w
            F = psums(y).real
            J = (np.array([k * y ** (k - 1) for k in (1, 2, 3)]) @ M).real
            if np.linalg.norm(F) < tol: break
            w = w - np.linalg.pinv(J) @ F
        if np.linalg.norm(F) < tol and np.all(np.isfinite(w)):
            return w / np.linalg.norm(w)
    raise RuntimeError

def basis_L(Q1, Q2, M):
    E = np.array([np.ones(9), Q1, Q2, Q1 ** 2, Q2 ** 2])
    _, sv, Vh = np.linalg.svd((E @ M).real)
    return M @ Vh[5:].T            # 9 x 4, columns span L (complex coords of real vectors)

def pencil(Q1, Q2, Lb):
    m = np.sum(Q1 * Q2).real; a = np.sum(Q1 ** 2 * Q2).real; b = np.sum(Q1 * Q2 ** 2).real
    G = lambda e: (Lb.T @ np.diag(e) @ Lb).real
    S1, SQ1, SQ2 = G(np.ones(9)), G(Q1), G(Q2)
    return m, a, b, a * S1 - 2 * m * SQ1, b * S1 - 2 * m * SQ2, S1

def disc_quartic(P1, P2):
    # det(P1 + t P2) as a polynomial in t (degree 4), by interpolation
    ts = np.arange(5) - 2.0
    vals = [np.linalg.det(P1 + t * P2) for t in ts]
    return np.polyfit(ts, vals, 4)

def s3val(Q1, Q2, U, m):
    return m * np.sum(U ** 3) - 3 * np.sum(Q1 * Q2 * U) * np.sum(U ** 2)

def p4_info(Q1, Q2, u):
    P = np.polynomial.polynomial
    tot = np.zeros(9, complex)
    for i in range(9):
        tot += P.polypow(np.array([Q1[i], u[i], Q2[i]]), 4)
    co = tot.real
    th = np.linspace(-np.pi / 2, np.pi / 2, 6001)[1:-1]; k = np.tan(th)
    vals = []
    for kap in k:
        q = Q1 + kap * u + kap ** 2 * Q2
        vals.append(np.sum(q ** 4).real / np.linalg.norm(q) ** 4)
    vals = np.array(vals)
    nsign = int(np.sum(np.diff(np.sign(vals)) != 0))
    return nsign, vals.min()

def gn(f, x, iters=300, tol=1e-12):
    mu = 1e-3
    F = f(x); nF = np.linalg.norm(F)
    for it in range(iters):
        if not np.isfinite(nF): return x, np.inf
        if nF < tol: break
        J = np.empty((len(F), len(x)))
        h = 1e-7
        for j in range(len(x)):
            e = np.zeros(len(x)); e[j] = h
            J[:, j] = (f(x + e) - f(x - e)) / (2 * h)
        while True:
            A = J.T @ J + mu * np.eye(len(x))
            dx = np.linalg.solve(A, J.T @ F)
            xn = x - dx; Fn = f(xn); nn = np.linalg.norm(Fn)
            if np.isfinite(nn) and nn < nF:
                x, F, nF = xn, Fn, nn; mu = max(mu / 3, 1e-12); break
            mu *= 4
            if mu > 1e8: return x, nF
        if nF < 1e-6:  # finish with minimum-norm Newton
            for k in range(6):
                J = np.empty((len(F), len(x)))
                for j in range(len(x)):
                    e = np.zeros(len(x)); e[j] = h
                    J[:, j] = (f(x + e) - f(x - e)) / (2 * h)
                x = x - np.linalg.lstsq(J, F, rcond=1e-10)[0]; F = f(x); nF = np.linalg.norm(F)
                if nF < tol: break
            break
    return x, nF

def run_line(r, starts, seed):
    rng = np.random.default_rng(seed)
    M = realmap(r)
    w1 = v3_point(rng, M); Q1 = M @ w1
    g = rng.normal(size=(2, 9))
    H = rng.normal(size=(3, 9))          # random slices to isolate points of R'
    tally = {}
    for st in range(starts):
        w2 = v3_point(rng, M)
        hc = H @ w2                       # slice through the start
        x1 = rng.normal(size=9); x2 = rng.normal(size=9)
        def f(z):
            w, a1, a2 = z[:9], z[9:18], z[18:27]
            Q2 = M @ w; U1 = M @ a1; U2 = M @ a2
            m = np.sum(Q1 * Q2); a = np.sum(Q1 ** 2 * Q2); b = np.sum(Q1 * Q2 ** 2)
            out = list(psums(Q2)) + [w @ w - 1] + list(H @ w - hc)
            for U in (U1, U2):
                out += [np.sum(e * U) for e in (np.ones(9), Q1, Q2, Q1 ** 2, Q2 ** 2)]
            for (X, Y) in ((U1, U1), (U1, U2), (U2, U2)):
                t1 = np.sum(X * Y); tq1 = np.sum(Q1 * X * Y); tq2 = np.sum(Q2 * X * Y)
                out += [a * t1 - 2 * m * tq1, b * t1 - 2 * m * tq2]
            out += [a1 @ g[0] - 1, a1 @ g[1], a2 @ g[0], a2 @ g[1] - 1]
            return np.real(np.array(out))
        z0 = np.concatenate([w2, x1, x2])
        z, res = gn(f, z0)
        if res > 1e-9: print(f'start {st}: no convergence ({res:.1e})'); continue
        w = z[:9]; Q2 = M @ w; U1 = M @ z[9:18]; U2 = M @ z[18:27]
        m = np.sum(Q1 * Q2).real
        # spurious check: line inside {A1 = 0}?
        A1s = [np.sum(X * Y).real for X, Y in ((U1, U1), (U1, U2), (U2, U2))]
        Lb = basis_L(Q1, Q2, M)
        mm, a, b, P1, P2, S1 = pencil(Q1, Q2, Lb)
        dq = disc_quartic(P1, P2)
        rts = np.roots(dq)
        # pattern: min distance between roots
        dmin = min(abs(rts[i] - rts[j]) for i in range(4) for j in range(i + 1, 4)) / (1 + max(abs(rts)))
        ranks = []
        for t in rts:
            sv = np.linalg.svd(P1 + t * P2, compute_uv=False)
            ranks.append(int(np.sum(sv > 1e-6 * sv[0])))
        # cubic on the line: U = U1 + t U2 (and U2)
        P = np.polynomial.polynomial
        ts = np.arange(4) - 1.5
        cv = [s3val(Q1, Q2, U1 + t * U2, m).real for t in ts]
        cco = np.polyfit(ts, cv, 3)
        cr = np.roots(cco)
        realpts = []
        for t in cr:
            if abs(t.imag) < 1e-8 * (1 + abs(t)):
                U = U1 + t.real * U2
                s = -np.sum(U ** 2).real / (2 * m)
                if s > 0:
                    u = U / np.sqrt(s)
                    ns, mn = p4_info(Q1, Q2, u)
                    realpts.append(('s>0', ns, round(mn, 3)))
                else:
                    realpts.append(('s<0',))
        print(f'start {st}: m={m:+.3f} A1 on line {np.round(A1s, 3)} disc roots sep {dmin:.1e} '
              f'ranks {ranks} real line pts {realpts}')
        key = ('m<0' if m < 0 else 'm>0', tuple(x[0] for x in realpts),
               sum(1 for x in realpts if len(x) > 1 and x[1] > 0))
        tally[key] = tally.get(key, 0) + 1
    print('tally:', sorted(tally.items()))

def run_rank2(r, starts, seed):
    rng = np.random.default_rng(seed)
    M = realmap(r)
    w1 = v3_point(rng, M); Q1 = M @ w1
    g = rng.normal(size=(2, 9))
    H = rng.normal(size=(3, 9))
    tally = {}
    for st in range(starts):
        w2 = v3_point(rng, M)
        hc = H @ w2
        x1 = rng.normal(size=9); x2 = rng.normal(size=9)
        th0 = rng.uniform(0, np.pi)
        def f(z):
            w, a1, a2, th = z[:9], z[9:18], z[18:27], z[27]
            Q2 = M @ w; U1 = M @ a1; U2 = M @ a2
            m = np.sum(Q1 * Q2); a = np.sum(Q1 ** 2 * Q2); b = np.sum(Q1 * Q2 ** 2)
            rho = np.cos(th) * (a - 2 * m * Q1) + np.sin(th) * (b - 2 * m * Q2)
            out = list(psums(Q2)) + [w @ w - 1] + list(H @ w - hc)
            E = np.array([np.ones(9), Q1, Q2, Q1 ** 2, Q2 ** 2])
            # rho*U_i must lie in span(E) (so Tr(rho U_i y) = 0 for y in L): residual of projection
            Eb = (E @ M).real  # real-coordinate version
            for U in (U1, U2):
                out += list(E @ U)
                v = rho * U    # complex coords of a real vector
                # coordinates of v in the real basis: M^{-1} v
                vr = np.linalg.solve(M, v)
                # project out span of real versions of E: T-orthogonality <-> Tr(v y)=0 for y in L
                # equivalently v is T-orthogonal to L; compute via L basis numerically
                out += list(Lperp_resid(Q1, Q2, M, v))
            out += [a1 @ g[0] - 1, a1 @ g[1], a2 @ g[0], a2 @ g[1] - 1]
            return np.real(np.array(out))
        z0 = np.concatenate([w2, x1, x2, [th0]])
        z, res = gn(f, z0)
        if res > 1e-9: print(f'start {st}: no convergence ({res:.1e})'); continue
        w = z[:9]; Q2 = M @ w; th = z[27]
        m = np.sum(Q1 * Q2).real
        Lb = basis_L(Q1, Q2, M)
        mm, a, b, P1, P2, S1 = pencil(Q1, Q2, Lb)
        Pr = np.cos(th) * P1 + np.sin(th) * P2
        ev = np.linalg.eigvalsh(Pr); evs = ev[np.argsort(-abs(ev))]
        sig = (int(np.sum(evs[:2] > 0)), int(np.sum(evs[:2] < 0)))
        dq = disc_quartic(P1, P2); rts = np.roots(dq)
        dmin = min(abs(rts[i] - rts[j]) for i in range(4) for j in range(i + 1, 4)) / (1 + max(abs(rts)))
        info = []
        if sig == (1, 1):
            # planes: Pr = l1 * l2 on L; find the two planes and conics
            evv, V = np.linalg.eigh(Pr)
            idx = np.argsort(-abs(evv))[:2]
            lp = [V[:, idx[0]] * np.sqrt(abs(evv[idx[0]])), V[:, idx[1]] * np.sqrt(abs(evv[idx[1]]))]
            # Pr = e+ v+v+^T - e- v-v-^T  => planes (v+ ± v-)·c = 0
            other = np.cos(th + 1.0) * P1 + np.sin(th + 1.0) * P2
            for sgn in (1, -1):
                nrm = lp[0] + sgn * lp[1]
                # basis of the plane nrm·c = 0
                _, _, Vh = np.linalg.svd(nrm[None, :]); B3 = Vh[1:].T  # 4 x 3
                Qc = B3.T @ other @ B3   # conic in the plane
                # parametrise conic: find a real point, then rational parametrisation numerically
                pts = conic_S3_points(Q1, Q2, Lb, B3, Qc, m)
                info.append(pts)
        print(f'start {st}: m={m:+.3f} rank-2 sig {sig} disc sep {dmin:.1e} conic data {info}')
        key = ('m<0' if m < 0 else 'm>0', sig,
               tuple(sum(1 for p in pts if p[0] == 's>0') for pts in info),
               tuple(sum(1 for p in pts if p[0] == 's>0' and p[1] > 0) for pts in info))
        tally[key] = tally.get(key, 0) + 1
    print('tally:', sorted(tally.items(), key=str))

_LPcache = {}
def Lperp_resid(Q1, Q2, M, v):
    E = np.array([np.ones(9), Q1, Q2, Q1 ** 2, Q2 ** 2]).T
    c = np.linalg.lstsq(E, v, rcond=None)[0]
    return np.linalg.solve(M, v - E @ c).real

def conic_S3_points(Q1, Q2, Lb, B3, Qc, m):
    # real conic Qc (3x3 sym) in plane coords; restrict S3 to it: 6 points.
    ev, V = np.linalg.eigh(Qc)
    if np.all(ev > 0) or np.all(ev < 0):
        return [('no real conic',)]
    # real point on conic: combine eigenvectors of opposite signs
    i = np.argmax(ev); j = np.argmin(ev)
    p0 = V[:, i] * np.sqrt(-ev[j]) + V[:, j] * np.sqrt(ev[i])
    # parametrise: line through p0 in direction d meets conic again at p0 + t d with
    # t = -2 p0^T Qc d / d^T Qc d; use pencil of directions d(θ) in a plane complementary
    _, _, Vh = np.linalg.svd(p0[None, :]); D2 = Vh[1:]
    def pt(phi):
        d = np.cos(phi) * D2[0] + np.sin(phi) * D2[1]
        den = d @ Qc @ d
        return den * p0 - 2 * (p0 @ Qc @ d) * d  # homogeneous, quadratic in (cos, sin)
    # S3 along the conic: degree 6 in (cos phi, sin phi); sample sign changes
    phis = np.linspace(0, np.pi, 4001)
    vals = []
    for ph in phis:
        c = B3 @ pt(ph); U = Lb @ c
        vals.append(s3val(Q1, Q2, U, m).real / np.linalg.norm(U) ** 3)
    vals = np.array(vals)
    out = []
    for k in np.where(np.diff(np.sign(vals)) != 0)[0]:
        lo, hi = phis[k], phis[k + 1]
        for _ in range(60):
            mid = (lo + hi) / 2
            vm = s3val(Q1, Q2, Lb @ (B3 @ pt(mid)), m).real
            vl = s3val(Q1, Q2, Lb @ (B3 @ pt(lo)), m).real
            if np.sign(vm) == np.sign(vl): lo = mid
            else: hi = mid
        U = Lb @ (B3 @ pt(lo))
        s = -np.sum(U ** 2).real / (2 * m)
        if s > 0:
            ns, mn = p4_info(Q1, Q2, U / np.sqrt(s))
            out.append(('s>0', ns, round(mn, 3)))
        else:
            out.append(('s<0',))
    return out

if __name__ == '__main__':
    mode, r, starts, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    (run_line if mode == 'line' else run_rank2)(r, starts, seed)
