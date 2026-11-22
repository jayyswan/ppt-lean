# Session 48: interval-arithmetic certificate for the S44.2 chain (r = 1 or 3).
# Usage: python3 cert48.py <r> <seed>        (self-contained; numpy + mpmath; writes nothing)
#
# Real model A = K (x) R = R^r x C^s, real coordinates u = [x_1..x_r, a_1, b_1, ..., a_s, b_s].
# Certifies (rigorously, mpmath.iv at 60 digits, Krawczyk) the four open real conditions of S48.1:
#  (C1) a real point Q* of V_3 = {p1 = p2 = p3 = 0} at which V_3 is smooth: 6 coordinates are fixed
#       dyadic rationals, the other 3 are enclosed in a box by a Krawczyk test;
#  (C2) a real root l* of the quintic det(l A1 + A2) (pencil of S_Q on the P^4 of line directions
#       L/Q, L = {Tr v = Tr Qv = Tr Q^2 v = 0}) that is simple (sign change + det' != 0 on the interval),
#       with inertia (3,2) on one side and (2,3) on the other, so the member has inertia (2,2,1);
#  (C3) a real point v* of C_Q = {A1 = A2 = p3 = 0} (Krawczyk in a chart, so C_Q is smooth there)
#       with M*(T,T) != 0 for its tangent T, M* = l* A1 + A2 (so v* is not a ramification point of
#       either ruling of the cone M* restricted to C_Q, and v* is not the vertex);
#  (C4) a simple real root k* of the quartic p4(Q* + k v*) (sign change + derivative != 0).
# All enclosures hold for every Q in the Q*-box simultaneously (interval parameters throughout).
import sys, numpy as np
from mpmath import mp, iv, mpf
from math import comb

r = int(sys.argv[1]); seed = int(sys.argv[2]); s = (9 - r) // 2
rng = np.random.default_rng(seed)
mp.dps = 60; iv.dps = 60
lo = lambda x: mpf(x.a); hi = lambda x: mpf(x.b)
def pos(x): return lo(x) > 0
def neg(x): return hi(x) < 0
def nz(x): return pos(x) or neg(x)

# ---------- algebra on the real model (works for float, mpf and iv entries) ----------
def mul(u, w):
    out = [u[i] * w[i] for i in range(r)]
    for j in range(s):
        a, b = u[r + 2 * j], u[r + 2 * j + 1]; c, d = w[r + 2 * j], w[r + 2 * j + 1]
        out += [a * c - b * d, a * d + b * c]
    return out
def tr(u):
    t = u[0]
    for i in range(1, r): t = t + u[i]
    for j in range(s): t = t + 2 * u[r + 2 * j]
    return t
def pw(u, k):
    out = u
    for _ in range(k - 1): out = mul(out, u)
    return out
def ps(u, k): return tr(pw(u, k))
def lin(cs, vs):  # sum c_i v_i
    out = [cs[0] * x for x in vs[0]]
    for c, v in zip(cs[1:], vs[1:]): out = [o + c * x for o, x in zip(out, v)]
    return out

# ---------- float search for a good sample (as in v4chain.py) ----------
def zc(u):
    x = u[:r]; w = u[r::2] + 1j * u[r + 1::2]
    return np.concatenate([x.astype(complex), w, np.conj(w)])
def jac3(u):
    z = zc(u); J = np.zeros((3, 9))
    for j in range(9):
        e = np.zeros(9); e[j] = 1; ze = zc(e)
        for k in range(3): J[k, j] = (k + 1) * np.sum(z ** k * ze).real
    return J
def v3_point():
    while True:
        u = rng.normal(size=9)
        for it in range(100):
            z = zc(u); F = np.array([np.sum(z ** k).real for k in (1, 2, 3)] + [u @ u - 1])
            J = np.vstack([jac3(u), 2 * u]); u = u + np.linalg.lstsq(J, -F, rcond=None)[0]
            if np.linalg.norm(F) < 1e-14: break
        z = zc(u)
        if np.isfinite(u).all() and np.linalg.norm(F) < 1e-12 and \
           min(abs(z[i] - z[j]) for i in range(9) for j in range(i)) > 1e-2:
            return u

def kernel_basis(Q, tools):
    # rows: v -> Tr(Q^k v), k = 0, 1, 2; pivots P (3 coords), free F (6); drop the free index with
    # the largest |Q_f| (so the 5 remaining vectors span a complement of Q in L)
    one = tools['one']; zero = tools['zero']
    rows = []
    for k in range(3):
        Qk = pw(Q, k) if k > 0 else [one] * r + sum([[one, zero] for _ in range(s)], [])
        row = [Qk[i] for i in range(r)]
        for j in range(s): row += [2 * Qk[r + 2 * j], -2 * Qk[r + 2 * j + 1]]
        rows.append(row)
    Pv, Fv, f0 = tools['piv']
    det3 = lambda M: (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
                      + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
    MP = [[rows[k][p] for p in Pv] for k in range(3)]; D = det3(MP)
    basis = []
    for f in Fv:
        if f == f0: continue
        rhs = [-rows[k][f] for k in range(3)]
        v = [zero] * 9; v[f] = one
        for c in range(3):
            Mc = [[(rhs[k] if cc == c else MP[k][cc]) for cc in range(3)] for k in range(3)]
            v[Pv[c]] = det3(Mc) / D
        basis.append(v)
    return basis, D

def forms(Q, B):
    n = len(B)
    prod = [[mul(B[i], B[j]) for j in range(n)] for i in range(n)]
    A1 = [[tr(prod[i][j]) for j in range(n)] for i in range(n)]
    A2 = [[tr(mul(Q, prod[i][j])) for j in range(n)] for i in range(n)]
    return A1, A2

def det_g(M):  # Gaussian elimination without pivoting (fine for generic matrices at these widths)
    M = [row[:] for row in M]; n = len(M); d = None
    for k in range(n):
        d = M[k][k] if d is None else d * M[k][k]
        for i in range(k + 1, n):
            f = M[i][k] / M[k][k]
            for j in range(k, n): M[i][j] = M[i][j] - f * M[k][j]
    return d
def pivots(M, perm):
    M = [[M[i][j] for j in perm] for i in perm]; n = len(M); out = []
    for k in range(n):
        out.append(M[k][k])
        for i in range(k + 1, n):
            f = M[i][k] / M[k][k]
            for j in range(k, n): M[i][j] = M[i][j] - f * M[k][j]
    return out

# ===================== float stage =====================
fl = dict(one=1.0, zero=0.0)
for attempt in range(200):
    Qf = v3_point()
    J = jac3(Qf)
    # unknown coordinates for the Krawczyk step on Q: best-conditioned 3 columns
    best = max(((a, b, c) for a in range(9) for b in range(a) for c in range(b)),
               key=lambda t: abs(np.linalg.det(J[:, list(t)])))
    # kernel pivots: rows of the linear map v -> Tr(Q^k v)
    Qfl = list(Qf)
    rows = np.array([[1.0] * r + [2.0, 0.0] * s, J[1] / 2, J[2] / 3])
    Pv = list(max(((a, b, c) for a in range(9) for b in range(a) for c in range(b)),
                  key=lambda t: abs(np.linalg.det(rows[:, list(t)]))))
    Fv = [j for j in range(9) if j not in Pv]
    f0 = max(Fv, key=lambda j: abs(Qf[j]))
    fl['piv'] = (Pv, Fv, f0)
    B, _ = kernel_basis(Qfl, fl); Bm = np.array(B)          # 5 x 9
    A1, A2 = map(np.array, forms(Qfl, B))
    # pencil roots
    ls = np.linspace(-3, 3, 11)
    co = np.polyfit(ls, [np.linalg.det(l * A1 + A2) for l in ls], 5)
    l22 = []
    for x in np.roots(co):
        if abs(x.imag) < 1e-9:
            ev = np.linalg.eigvalsh(x.real * A1 + A2); ev = ev[np.argsort(abs(ev))][1:]
            if (ev > 0).sum() == 2: l22.append(x.real)
    if not l22: continue
    lam = l22[0]; Mst = lam * A1 + A2
    # real points of C_Q in coordinates c (v = c @ Bm)
    C3 = lambda c: ps(list(c @ Bm), 3)
    def Fc(c): return np.array([c @ A1 @ c, c @ A2 @ c, C3(c), c @ c - 1])
    def Jc(c):
        g = np.zeros(5); h = 1e-7
        for i in range(5):
            e = np.zeros(5); e[i] = h; g[i] = (C3(c + e) - C3(c - e)) / (2 * h)
        return np.vstack([2 * A1 @ c, 2 * A2 @ c, g, 2 * c])
    found = None
    for st in range(300):
        c = rng.normal(size=5); c /= np.linalg.norm(c)
        for it in range(60):
            F = Fc(c); c = c + np.linalg.lstsq(Jc(c), -F, rcond=None)[0]
            if not np.isfinite(c).all() or np.linalg.norm(F) < 1e-13: break
        if not np.isfinite(c).all() or np.linalg.norm(Fc(c)) > 1e-11: continue
        v = c @ Bm
        cq = [comb(4, m) * tr(mul(pw(list(Qf), 4 - m), pw(list(v), m))) if 0 < m < 4 else
              (ps(list(Qf), 4) if m == 0 else ps(list(v), 4)) for m in range(5)]
        rts = [x.real for x in np.roots(cq[::-1]) if abs(x.imag) < 1e-9]
        if not rts: continue
        # tangent and M*(T,T)
        Jt = Jc(c)[:3]; T = np.linalg.svd(np.vstack([Jt, c]))[2][-1]
        mtt = abs(T @ Mst @ T) / np.linalg.norm(Mst, 2)
        if mtt < 1e-2: continue
        dq = np.polyder(np.poly1d(cq[::-1]))
        k0 = max(rts, key=lambda k: abs(dq(k)) / (1 + abs(k)) ** 3)
        found = (c, T, k0); break
    if found: break
print(f'r = {r}, seed {seed}: float sample found at attempt {attempt}; l* ~ {lam:.6f}')
cf, Tf, kf = found

# ===================== rigorous stage =====================
ivt = dict(one=iv.mpf(1), zero=iv.mpf(0), piv=fl['piv'])
D60 = mpf(2) ** -60
def dyad(x): return mpf(int(round(x / float(D60)))) * D60

# (C1) Q*: fix 6 coordinates as dyadic rationals; solve p1 = p2 = p3 = 0 for the 3 in `best`
unk = list(best); fixed = [j for j in range(9) if j not in unk]
Qm = [dyad(x) for x in Qf]
def F3(u): return [ps(u, 1), ps(u, 2), ps(u, 3)]
def J3(u):  # exact partial derivatives d p_k / d u_j for j in unk (k*Tr(u^{k-1} e_j))
    out = []
    for k in (1, 2, 3):
        uk = pw(u, k - 1) if k > 1 else None
        row = []
        for j in unk:
            e = [0] * 9; e[j] = 1
            e = [ivt['one'] if x == 1 else ivt['zero'] for x in e] if isinstance(u[0], iv.mpf) else [mpf(x) for x in e]
            row.append(k * tr(mul(uk, e)) if k > 1 else tr(e))
        out.append(row)
    return out
def solve3(M, b):  # Cramer (works for mp and iv)
    d3 = lambda A: (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
                    + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    D = d3(M)
    return [d3([[(b[k] if cc == c else M[k][cc]) for cc in range(3)] for k in range(3)]) / D for c in range(3)]
for it in range(40):   # Newton at 60 digits on the unknown coordinates
    Fm = F3(Qm); dx = solve3(J3(Qm), [-x for x in Fm])
    for c, j in enumerate(unk): Qm[j] += dx[c]
    if max(abs(x) for x in Fm) < mpf(10) ** -55: break

def krawczyk(Fun, Jac, xm, rad, label):
    """Krawczyk test for a square system with interval parameters. xm: midpoint (mpf list),
    Fun(x) -> interval values at the point x, Jac(X) -> interval Jacobian on the box X."""
    n = len(xm)
    X = [iv.mpf([xm[i] - rad, xm[i] + rad]) for i in range(n)]
    Jm = Jac([iv.mpf(x) for x in xm])
    Jmid = mp.matrix([[ (lo(Jm[i][j]) + hi(Jm[i][j])) / 2 for j in range(n)] for i in range(n)])
    Y = Jmid ** -1
    Fx = Fun([iv.mpf(x) for x in xm]); JX = Jac(X)
    K = []
    for i in range(n):
        t = iv.mpf(xm[i])
        for k in range(n): t = t - iv.mpf(Y[i, k]) * Fx[k]
        for j in range(n):
            a = (iv.mpf(1) if i == j else iv.mpf(0))
            for k in range(n): a = a - iv.mpf(Y[i, k]) * JX[k][j]
            t = t + a * (X[j] - iv.mpf(xm[j]))
        K.append(t)
    ok = all(lo(K[i]) > lo(X[i]) and hi(K[i]) < hi(X[i]) for i in range(n))
    print(f'  Krawczyk [{label}]: n = {n}, radius {float(rad):.1e}: K(X) in int(X) = {ok}')
    return ok, K

def Qbox(xs):
    u = [iv.mpf(Qm[j]) for j in range(9)]
    for c, j in enumerate(unk): u[j] = xs[c]
    return u
okQ, KQ = krawczyk(lambda xs: F3(Qbox(xs)), lambda xs: J3(Qbox(xs)), [Qm[j] for j in unk], mpf(10) ** -40, 'C1: Q* on V_3')
QI = Qbox(KQ)   # interval enclosure of the true Q* (all later quantities hold for every Q in it)
print(f'  Q* fixed coords (dyadic, 2^-60): {fixed}; enclosure width {float(max(hi(x) - lo(x) for x in QI)):.1e}')

# basis of L/Q and the forms, as intervals
BI, DI = kernel_basis(QI, ivt)
A1I, A2I = forms(QI, BI)
print(f'  kernel pivot determinant excludes 0: {nz(DI)}')

# (C2) the pencil root
def detI(l):
    lI = iv.mpf(l) if not isinstance(l, iv.mpf) else l
    return det_g([[lI * A1I[i][j] + A2I[i][j] for j in range(5)] for i in range(5)])
lm = mp.findroot(lambda l: mpf(lo(detI(iv.mpf(l)))) / 2 + mpf(hi(detI(iv.mpf(l)))) / 2, mpf(lam))
dl = mpf(10) ** -25; la, lb = lm - dl, lm + dl
da, db = detI(la), detI(lb)
sign_change = (pos(da) and neg(db)) or (neg(da) and pos(db))
# det' on [la, lb]: interpolate det at 6 integer nodes (exact Lagrange coefficients), differentiate
nodes = [-3, -2, -1, 0, 1, 2]
vals = [detI(mpf(t)) for t in nodes]
def lagr_deriv(Lam):
    tot = iv.mpf(0)
    for k, tk in enumerate(nodes):
        others = [t for t in nodes if t != tk]
        den = 1
        for t in others: den *= (tk - t)
        dsum = iv.mpf(0)
        for drop in others:
            p = iv.mpf(1)
            for t in others:
                if t != drop: p = p * (Lam - t)
            dsum = dsum + p
        tot = tot + vals[k] * dsum / den
    return tot
dprime = lagr_deriv(iv.mpf([la, lb]))
def inertia(l):
    M = [[iv.mpf(l) * A1I[i][j] + A2I[i][j] for j in range(5)] for i in range(5)]
    for t in range(50):
        perm = list(rng.permutation(5)) if t else list(range(5))
        pv = pivots(M, perm)
        if all(nz(p) for p in pv):
            return (sum(pos(p) for p in pv), sum(neg(p) for p in pv))
    return None
ia, ib = inertia(la), inertia(lb)
okP = sign_change and nz(dprime) and sorted([ia, ib]) == [(2, 3), (3, 2)]
print(f'  C2: l* in [{float(la):.12f}, {float(lb):.12f}]; det sign change {sign_change}; det\' excludes 0 {nz(dprime)};'
      f' inertia left {ia}, right {ib}  ->  member of inertia (2,2,1): {okP}')

# (C3) a point v* of C_Q in a chart: c[k0] = 1, c[k1] = dyadic, unknowns the other three
cf = cf / cf[np.argmax(abs(cf))]; Tf2 = Tf - Tf[np.argmax(abs(cf))] * cf  # tangent with chart coord 0
k0 = int(np.argmax(abs(cf))); Tf2 = Tf2 / np.linalg.norm(Tf2)
k1 = int(max((k for k in range(5) if k != k0), key=lambda k: abs(Tf2[k])))
un2 = [k for k in range(5) if k not in (k0, k1)]
cfix = {k0: mpf(1), k1: dyad(cf[k1])}
def cvec(xs):
    c = [None] * 5
    for k, val in cfix.items(): c[k] = iv.mpf(val)
    for i, k in enumerate(un2): c[k] = xs[i]
    return c
def q(Mx, a, b): return sum((a[i] * Mx[i][j] * b[j] for i in range(5) for j in range(5)), iv.mpf(0))
def Fv(xs):
    c = cvec(xs); v = lin(c, BI)
    return [q(A1I, c, c), q(A2I, c, c), ps(v, 3)]
def Jv(xs):
    c = cvec(xs); v = lin(c, BI); v2 = mul(v, v); out = [[], [], []]
    for k in un2:
        out[0].append(2 * sum((A1I[k][j] * c[j] for j in range(5)), iv.mpf(0)))
        out[1].append(2 * sum((A2I[k][j] * c[j] for j in range(5)), iv.mpf(0)))
        out[2].append(3 * tr(mul(v2, BI[k])))
    return out
# float -> 60-digit Newton on the chart
cm = [mpf(float(cf[k])) for k in un2]
for it in range(40):
    Fm = [ (lo(x) + hi(x)) / 2 for x in Fv([iv.mpf(x) for x in cm])]
    Jm = [[(lo(x) + hi(x)) / 2 for x in row] for row in Jv([iv.mpf(x) for x in cm])]
    dx = solve3(Jm, [-x for x in Fm]); cm = [a + b for a, b in zip(cm, dx)]
    if max(abs(x) for x in Fm) < mpf(10) ** -50: break
okC, KC = krawczyk(Fv, Jv, cm, mpf(10) ** -30, 'C3: v* on C_Q')
cI = cvec(KC); vI = lin(cI, BI)
# tangent T in the chart: T[k0] = 0, T[k1] = 1, J_un T_un = -J_k1
def colk(c, k):
    v = lin(c, BI); v2 = mul(v, v)
    return [2 * sum((A1I[k][j] * c[j] for j in range(5)), iv.mpf(0)),
            2 * sum((A2I[k][j] * c[j] for j in range(5)), iv.mpf(0)), 3 * tr(mul(v2, BI[k]))]
JU = Jv(KC); Jk1 = colk(cI, k1)
Tun = solve3(JU, [-x for x in Jk1])
T = [iv.mpf(0)] * 5; T[k1] = iv.mpf(1)
for i, k in enumerate(un2): T[k] = Tun[i]
LamI = iv.mpf([la, lb])
MI = [[LamI * A1I[i][j] + A2I[i][j] for j in range(5)] for i in range(5)]
mTT = q(MI, T, T)
Mv = [sum((MI[i][j] * cI[j] for j in range(5)), iv.mpf(0)) for i in range(5)]
notvertex = any(nz(x) for x in Mv)
print(f'  C3: M*(T,T) in [{float(lo(mTT)):.6g}, {float(hi(mTT)):.6g}] excludes 0: {nz(mTT)}; v* not the vertex: {notvertex}')

# (C4) p4 on the line Q* + k v*
P4 = [ps(QI, 4)] + [comb(4, m) * tr(mul(pw(QI, 4 - m), pw(vI, m))) for m in (1, 2, 3)] + [ps(vI, 4)]
def p4at(K): return sum((P4[m] * K ** m for m in range(5)), iv.mpf(0))
def dp4at(K): return sum((m * P4[m] * K ** (m - 1) for m in range(1, 5)), iv.mpf(0))
P4m = [(lo(x) + hi(x)) / 2 for x in P4]
km = mp.findroot(lambda K: sum(P4m[m] * K ** m for m in range(5)), mpf(kf))
dk = mpf(10) ** -20; ka, kb = km - dk, km + dk
pa, pb = p4at(iv.mpf(ka)), p4at(iv.mpf(kb))
sc4 = (pos(pa) and neg(pb)) or (neg(pa) and pos(pb))
d4 = dp4at(iv.mpf([ka, kb]))
print(f'  C4: k* in [{float(ka):.12f}, {float(kb):.12f}]; p4 sign change {sc4}; p4\' excludes 0 {nz(d4)}')
allok = okQ and nz(DI) and okP and okC and nz(mTT) and notvertex and sc4 and nz(d4)
# report the resulting point y = Q* + k* v* of V_4 (float view)
y = [float((lo(a) + hi(a)) / 2) + float(km) * float((lo(b) + hi(b)) / 2) for a, b in zip(QI, vI)]
nrm = np.linalg.norm(y); zy = zc(np.array(y))
print(f'  y = Q* + k* v*: normalised p1..p5 = {[round(np.sum(zy ** k).real / nrm ** k, 12) for k in range(1, 6)]}; '
      f'real roots of charpoly {int(sum(abs(np.roots(np.poly(zy)).imag) < 1e-7))}')
print(f'CERTIFIED r = {r}: {allok}')
