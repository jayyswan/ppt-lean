# Session 44: the V_4 route (kill p1..p4, then the x^9 = quartic engine) for r < 9.
# Usage: python3 v4chain.py <r> <nQ> <seed>
# K (x) R = R^r x C^s, r + 2s = 9.  For nQ random real points Q of V_3 = {p1=p2=p3=0}:
#  - the direction space of lines through Q in V_3 (P^4 after 3 linear conditions),
#  - real points of C_Q = {q1 = q2 = c = 0} (q1 = p2(v), q2 = sum zQ zv^2, c = p3(v)),
#  - real roots of p4 on each real line Q + k v,
#  - the singular members of the pencil l*A1 + A2 (quintic) and their signatures.
import sys, numpy as np
from math import comb

r = int(sys.argv[1]); nQ = int(sys.argv[2]); seed = int(sys.argv[3])
s = (9 - r) // 2
mode = sys.argv[4] if len(sys.argv) > 4 else 'v3'
KS = (1, 2, 3, 4) if mode == 'v4' else (1, 2, 3)
rng = np.random.default_rng(seed)

def zc(u):
    x = u[:r]; w = u[r::2] + 1j * u[r + 1::2]
    return np.concatenate([x.astype(complex), w, np.conj(w)])

def lin_rows(Q):
    # real linear maps v -> sum zQ^m zv for m = 0, 1, 2 (p1, p2-polar, p3-polar)
    rows = []
    for m in range(3):
        row = []
        for j in range(9):
            e = np.zeros(9); e[j] = 1
            row.append(np.sum(zc(Q) ** m * zc(e)).real)
        rows.append(row)
    return np.array(rows)

def psum(z, k): return np.sum(z ** k).real

def v3_point():
    for _ in range(200):
        u = rng.normal(size=9)
        for it in range(200):
            z = zc(u)
            F = np.array([psum(z, k) for k in KS] + [u @ u - 1])
            J = np.zeros((len(KS) + 1, 9))
            for j in range(9):
                e = np.zeros(9); e[j] = 1; ze = zc(e)
                J[0, j] = np.sum(ze).real
                J[1, j] = 2 * np.sum(z * ze).real
                J[2, j] = 3 * np.sum(z ** 2 * ze).real
                if len(KS) == 4: J[3, j] = 4 * np.sum(z ** 3 * ze).real
            J[-1] = 2 * u
            du = np.linalg.lstsq(J, -F, rcond=None)[0]
            u = u + du
            if np.linalg.norm(F) < 1e-14: break
        if np.linalg.norm(F) < 1e-12 and np.isfinite(u).all():
            z = zc(u)
            if min(abs(z[i] - z[j]) for i in range(9) for j in range(i)) > 1e-3:
                return u
    return None

def frame(Q):
    L = lin_rows(Q)
    # null space of L (6-dim, contains Q), then orthogonal complement of Q in it
    _, S, Vt = np.linalg.svd(L)
    N = Vt[3:].T            # 9 x 6
    Qn = Q / np.linalg.norm(Q)
    N = N - np.outer(Qn, Qn @ N)
    U, S2, _ = np.linalg.svd(N)
    return U[:, :5]          # 9 x 5 orthonormal, orthogonal to Q

def forms(Q, E):
    # quadric matrices A1 (p2(v)), A2 (sum zQ zv^2) on t in R^5, and cubic tensor
    zQ = zc(Q); Z = np.array([zc(E[:, j]) for j in range(5)])  # 5 x 9 complex
    A1 = np.real(Z @ Z.T)
    A2 = np.real((Z * zQ) @ Z.T)
    C3 = np.real(np.einsum('ai,bi,ci->abc', Z, Z, Z))
    return A1, A2, C3, Z

def cq_points(A1, A2, C3, nstart=400):
    pts = []
    for _ in range(nstart):
        t = rng.normal(size=5); t /= np.linalg.norm(t)
        ok = False
        for it in range(80):
            F = np.array([t @ A1 @ t, t @ A2 @ t, np.einsum('abc,a,b,c', C3, t, t, t), t @ t - 1])
            J = np.vstack([2 * A1 @ t, 2 * A2 @ t, 3 * np.einsum('abc,b,c->a', C3, t, t), 2 * t])
            dt = np.linalg.lstsq(J, -F, rcond=None)[0]
            t = t + dt
            if not np.isfinite(t).all(): break
            if np.linalg.norm(F) < 1e-13: ok = True; break
        if ok:
            pts.append(t / np.linalg.norm(t))
    return pts

def p4_roots(Q, v):
    zQ, zv = zc(Q), zc(v)
    co = [comb(4, m) * np.sum(zQ ** (4 - m) * zv ** m).real for m in range(5)]  # coeff of k^m
    rts = np.roots(co[::-1])
    return [x.real for x in rts if abs(x.imag) < 1e-9 * (1 + abs(x))], co

def pencil(A1, A2):
    # det(l A1 + A2) as a polynomial in l (degree 5), by interpolation
    ls = np.linspace(-3, 3, 11)
    d = [np.linalg.det(l * A1 + A2) for l in ls]
    co = np.polyfit(ls, d, 5)
    rts = np.roots(co)
    out = []
    for x in rts:
        if abs(x.imag) < 1e-8 * (1 + abs(x)):
            l = x.real
            ev = np.linalg.eigvalsh(l * A1 + A2)
            ev = ev[np.argsort(abs(ev))][1:]   # drop the zero eigenvalue
            out.append((l, int((ev > 0).sum()), int((ev < 0).sum())))
    return len(rts), out

tot_real_C = 0; tot_p4 = 0; sig22 = 0
for q in range(nQ):
    Q = v3_point()
    if Q is None: print('no V3 point'); continue
    E = frame(Q)
    A1, A2, C3, Z = forms(Q, E)
    eig1 = np.linalg.eigvalsh(A1)
    pts = cq_points(A1, A2, C3)
    # distinct real points of C_Q (up to sign)
    dist = []
    for t in pts:
        if all(min(np.linalg.norm(t - d), np.linalg.norm(t + d)) > 1e-6 for d in dist): dist.append(t)
    nrl = []
    for t in dist:
        v = E @ t
        rts, co = p4_roots(Q, v)
        nrl.append(len(rts))
    deg, pen = pencil(A1, A2)
    has22 = any(a == 2 and b == 2 for _, a, b in pen)
    tot_real_C += len(dist) > 0; tot_p4 += any(n > 0 for n in nrl); sig22 += has22
    print(f'Q{q}: sig(p2 on dirs) = ({(eig1>0).sum()},{(eig1<0).sum()}); real pts of C_Q found: {len(dist)};'
          f' p4 real-root counts: { {k: nrl.count(k) for k in set(nrl)} }; real singular members (l, +, -): '
          + ', '.join(f'({l:.3g},{a},{b})' for l, a, b in pen))
print(f'r={r}: C_Q(R) nonempty {tot_real_C}/{nQ}; some line with real p4 root {tot_p4}/{nQ}; (2,2) member {sig22}/{nQ}')
