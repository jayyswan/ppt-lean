# Session 49: interval-arithmetic certificate for the DECIC V_4 chain (n = 10), engine x^10 = quartic.
# Usage: python3 cert49.py <r> <seed> [maxattempts] [n]   (default n = 10; r in {2, 4, 6} for n = 10;
#        any n >= 9 works: k = n - 8 extra chart coordinates, Gram matrix of size k; self-contained; writes nothing)
# Session 50 addition: at the end, interval enclosures of the real coordinates of y = Q* + k* v* and a check that
# two of them differ (so the K-part of y is not in P when A = K x P(i)^t is a padded algebra, S50.2).
#
# Real model A = K (x) R = R^r x C^s (r + 2s = 10), real coordinates u = [x_1..x_r, a_1, b_1, ..., a_s, b_s].
# Certifies (mpmath.iv at 60 digits, Krawczyk) the open real conditions of S49.2:
#  (C1) a real point Q* of V_3 = {p1 = p2 = p3 = 0} at which V_3 is smooth (7 dyadic coordinates fixed,
#       3 enclosed by Krawczyk);
#  (C2) a simple real root l* of the sextic det(l A1 + A2) (pencil on the P^5 of line directions L/Q),
#       with inertia on the two sides such that the member has inertia (3,2,1) or (2,3,1) (rank-5 cone over
#       a quadric of index 2 in P^4: real planes through the vertex);
#  (C3) a real point v* of the surface C_Q = {A1 = A2 = p3 = 0} (Krawczyk in a chart with 2 extra fixed
#       coordinates, so C_Q is smooth there), with M*v* != 0 (not the vertex) and det Gram_M*(T1, T2) != 0
#       for a basis T1, T2 of the tangent plane (rank 2: the vertex is not in the tangent space, so some real
#       M*-isotropic plane through the vertex and v* meets C_Q transversally at v*);
#  (C4) a simple real root k* of the quartic p4(Q* + k v*).
# For r = 6 the float stage is expected to fail (sign lemma analogue); maxattempts bounds the search.
import sys, numpy as np
from mpmath import mp, iv, mpf
from math import comb

n = int(sys.argv[4]) if len(sys.argv) > 4 else 10
r = int(sys.argv[1]); seed = int(sys.argv[2]); s = (n - r) // 2
maxatt = int(sys.argv[3]) if len(sys.argv) > 3 else 400
kk = n - 8                    # dim C_Q (number of tangent vectors / extra fixed chart coordinates)
m = n - 4                     # dim L/Q
rng = np.random.default_rng(seed)
mp.dps = 60; iv.dps = 60
lo = lambda x: mpf(x.a); hi = lambda x: mpf(x.b)
def pos(x): return lo(x) > 0
def neg(x): return hi(x) < 0
def nz(x): return pos(x) or neg(x)

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
def lin(cs, vs):
    out = [cs[0] * x for x in vs[0]]
    for c, v in zip(cs[1:], vs[1:]): out = [o + c * x for o, x in zip(out, v)]
    return out

def zc(u):
    x = u[:r]; w = u[r::2] + 1j * u[r + 1::2]
    return np.concatenate([x.astype(complex), w, np.conj(w)])
def jac3(u):
    z = zc(u); J = np.zeros((3, n))
    for j in range(n):
        e = np.zeros(n); e[j] = 1; ze = zc(e)
        for k in range(3): J[k, j] = (k + 1) * np.sum(z ** k * ze).real
    return J
def v3_point():
    while True:
        u = rng.normal(size=n)
        for it in range(100):
            z = zc(u); F = np.array([np.sum(z ** k).real for k in (1, 2, 3)] + [u @ u - 1])
            J = np.vstack([jac3(u), 2 * u]); u = u + np.linalg.lstsq(J, -F, rcond=None)[0]
            if np.linalg.norm(F) < 1e-14: break
        z = zc(u)
        if np.isfinite(u).all() and np.linalg.norm(F) < 1e-12 and \
           min(abs(z[i] - z[j]) for i in range(n) for j in range(i)) > 1e-2:
            return u

def det3(M):
    return (M[0][0] * (M[1][1] * M[2][2] - M[1][2] * M[2][1]) - M[0][1] * (M[1][0] * M[2][2] - M[1][2] * M[2][0])
            + M[0][2] * (M[1][0] * M[2][1] - M[1][1] * M[2][0]))
def solve3(M, b):
    D = det3(M)
    return [det3([[(b[k] if cc == c else M[k][cc]) for cc in range(3)] for k in range(3)]) / D for c in range(3)]

def kernel_basis(Q, tools):
    one = tools['one']; zero = tools['zero']
    rows = []
    for k in range(3):
        Qk = pw(Q, k) if k > 0 else [one] * r + sum([[one, zero] for _ in range(s)], [])
        row = [Qk[i] for i in range(r)]
        for j in range(s): row += [2 * Qk[r + 2 * j], -2 * Qk[r + 2 * j + 1]]
        rows.append(row)
    Pv, Fv, f0 = tools['piv']
    MP = [[rows[k][p] for p in Pv] for k in range(3)]; D = det3(MP)
    basis = []
    for f in Fv:
        if f == f0: continue
        rhs = [-rows[k][f] for k in range(3)]
        v = [zero] * n; v[f] = one
        for c in range(3):
            Mc = [[(rhs[k] if cc == c else MP[k][cc]) for cc in range(3)] for k in range(3)]
            v[Pv[c]] = det3(Mc) / D
        basis.append(v)
    return basis, D

def forms(Q, B):
    k = len(B)
    prod = [[mul(B[i], B[j]) for j in range(k)] for i in range(k)]
    return ([[tr(prod[i][j]) for j in range(k)] for i in range(k)],
            [[tr(mul(Q, prod[i][j])) for j in range(k)] for i in range(k)])

def det_g(M):
    M = [row[:] for row in M]; k = len(M); d = None
    for a in range(k):
        d = M[a][a] if d is None else d * M[a][a]
        for i in range(a + 1, k):
            f = M[i][a] / M[a][a]
            for j in range(a, k): M[i][j] = M[i][j] - f * M[a][j]
    return d
def pivots(M, perm):
    M = [[M[i][j] for j in perm] for i in perm]; k = len(M); out = []
    for a in range(k):
        out.append(M[a][a])
        for i in range(a + 1, k):
            f = M[i][a] / M[a][a]
            for j in range(a, k): M[i][j] = M[i][j] - f * M[a][j]
    return out

def good_member(ev):
    p = int((ev > 0).sum()); q = int((ev < 0).sum())
    return min(p, q) >= 2

# ===================== float stage =====================
fl = dict(one=1.0, zero=0.0)
stats = dict(Q=0, pencil=0, CQ=0, p4real=0, p4none=0)
found = None
for attempt in range(maxatt):
    Qf = v3_point(); stats['Q'] += 1
    J = jac3(Qf)
    best = max(((a, b, c) for a in range(n) for b in range(a) for c in range(b)),
               key=lambda t: abs(np.linalg.det(J[:, list(t)])))
    rows = np.array([[1.0] * r + [2.0, 0.0] * s, J[1] / 2, J[2] / 3])
    Pv = list(max(((a, b, c) for a in range(n) for b in range(a) for c in range(b)),
                  key=lambda t: abs(np.linalg.det(rows[:, list(t)]))))
    Fv = [j for j in range(n) if j not in Pv]
    f0 = max(Fv, key=lambda j: abs(Qf[j]))
    fl['piv'] = (Pv, Fv, f0)
    B, _ = kernel_basis(list(Qf), fl); Bm = np.array(B)
    A1, A2 = map(np.array, forms(list(Qf), B))
    ls = np.linspace(-3, 3, 15)
    co = np.polyfit(ls, [np.linalg.det(l * A1 + A2) for l in ls], m)
    cand = []
    for x in np.roots(co):
        if abs(x.imag) < 1e-9:
            ev = np.linalg.eigvalsh(x.real * A1 + A2); ev = ev[np.argsort(abs(ev))][1:]
            if good_member(ev): cand.append(x.real)
    if not cand: continue
    stats['pencil'] += 1
    for lam in cand:
        Mst = lam * A1 + A2
        C3 = lambda c: ps(list(c @ Bm), 3)
        def Fc(c): return np.array([c @ A1 @ c, c @ A2 @ c, C3(c), c @ c - 1])
        def Jc(c):
            g = np.zeros(m); h = 1e-7
            for i in range(m):
                e = np.zeros(m); e[i] = h; g[i] = (C3(c + e) - C3(c - e)) / (2 * h)
            return np.vstack([2 * A1 @ c, 2 * A2 @ c, g, 2 * c])
        for st in range(150):
            c = rng.normal(size=m); c /= np.linalg.norm(c)
            for it in range(60):
                F = Fc(c); c = c + np.linalg.lstsq(Jc(c), -F, rcond=None)[0]
                if not np.isfinite(c).all() or np.linalg.norm(F) < 1e-13: break
            if not np.isfinite(c).all() or np.linalg.norm(Fc(c)) > 1e-11: continue
            stats['CQ'] += 1
            v = c @ Bm
            cq = [comb(4, k) * tr(mul(pw(list(Qf), 4 - k), pw(list(v), k))) if 0 < k < 4 else
                  (ps(list(Qf), 4) if k == 0 else ps(list(v), 4)) for k in range(5)]
            rts = [x.real for x in np.roots(cq[::-1]) if abs(x.imag) < 1e-9]
            if not rts: stats['p4none'] += 1; continue
            stats['p4real'] += 1
            Tn = np.linalg.svd(np.vstack([Jc(c)[:3], c]))[2][4:]   # tangent space (m - 4 = kk vectors)
            G = Tn @ Mst @ Tn.T; gd = abs(np.linalg.det(G)) / np.linalg.norm(Mst, 2) ** 2
            if gd < 1e-3: continue
            if np.linalg.norm(Mst @ c) / np.linalg.norm(Mst, 2) < 1e-3: continue
            dq = np.polyder(np.poly1d(cq[::-1]))
            k0 = max(rts, key=lambda k: abs(dq(k)) / (1 + abs(k)) ** 3)
            found = (lam, c, k0); break
        if found: break
    if found: break
print(f'r = {r}, seed {seed}: float stats {stats}')
if not found:
    print(f'no float sample in {maxatt} attempts'); print(f'CERTIFIED n = {n}, r = {r}: False'); sys.exit()
lam, cf, kf = found
print(f'float sample at attempt {attempt}; l* ~ {lam:.6f}')

# ===================== rigorous stage =====================
ivt = dict(one=iv.mpf(1), zero=iv.mpf(0), piv=fl['piv'])
D60 = mpf(2) ** -60
def dyad(x): return mpf(int(round(x / float(D60)))) * D60

unk = list(best); fixed = [j for j in range(n) if j not in unk]
Qm = [dyad(x) for x in Qf]
def F3(u): return [ps(u, 1), ps(u, 2), ps(u, 3)]
def J3(u):
    out = []
    isiv = isinstance(u[0], iv.mpf)
    for k in (1, 2, 3):
        uk = pw(u, k - 1) if k > 1 else None
        row = []
        for j in unk:
            e = [(ivt['one'] if i == j else ivt['zero']) if isiv else (mpf(1) if i == j else mpf(0)) for i in range(n)]
            row.append(k * tr(mul(uk, e)) if k > 1 else tr(e))
        out.append(row)
    return out
for it in range(40):
    Fm = F3(Qm); dx = solve3(J3(Qm), [-x for x in Fm])
    for c, j in enumerate(unk): Qm[j] += dx[c]
    if max(abs(x) for x in Fm) < mpf(10) ** -55: break

def krawczyk(Fun, Jac, xm, rad, label):
    k = len(xm)
    X = [iv.mpf([xm[i] - rad, xm[i] + rad]) for i in range(k)]
    Jm = Jac([iv.mpf(x) for x in xm])
    Jmid = mp.matrix([[(lo(Jm[i][j]) + hi(Jm[i][j])) / 2 for j in range(k)] for i in range(k)])
    Y = Jmid ** -1
    Fx = Fun([iv.mpf(x) for x in xm]); JX = Jac(X)
    K = []
    for i in range(k):
        t = iv.mpf(xm[i])
        for a in range(k): t = t - iv.mpf(Y[i, a]) * Fx[a]
        for j in range(k):
            b = (iv.mpf(1) if i == j else iv.mpf(0))
            for a in range(k): b = b - iv.mpf(Y[i, a]) * JX[a][j]
            t = t + b * (X[j] - iv.mpf(xm[j]))
        K.append(t)
    ok = all(lo(K[i]) > lo(X[i]) and hi(K[i]) < hi(X[i]) for i in range(k))
    print(f'  Krawczyk [{label}]: n = {k}, radius {float(rad):.1e}: K(X) in int(X) = {ok}')
    return ok, K

def Qbox(xs):
    u = [iv.mpf(Qm[j]) for j in range(n)]
    for c, j in enumerate(unk): u[j] = xs[c]
    return u
okQ, KQ = krawczyk(lambda xs: F3(Qbox(xs)), lambda xs: J3(Qbox(xs)), [Qm[j] for j in unk], mpf(10) ** -40, 'C1: Q* on V_3')
QI = Qbox(KQ)
BI, DI = kernel_basis(QI, ivt)
A1I, A2I = forms(QI, BI)
print(f'  kernel pivot determinant excludes 0: {nz(DI)}')

def detI(l):
    lI = iv.mpf(l) if not isinstance(l, iv.mpf) else l
    return det_g([[lI * A1I[i][j] + A2I[i][j] for j in range(m)] for i in range(m)])
lm = mp.findroot(lambda l: mpf(lo(detI(iv.mpf(l)))) / 2 + mpf(hi(detI(iv.mpf(l)))) / 2, mpf(lam))
dl = mpf(10) ** -25; la, lb = lm - dl, lm + dl
da, db = detI(la), detI(lb)
sign_change = (pos(da) and neg(db)) or (neg(da) and pos(db))
nodes = list(range(-3, m - 2))       # m + 1 nodes, det has degree m in l
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
    M = [[iv.mpf(l) * A1I[i][j] + A2I[i][j] for j in range(m)] for i in range(m)]
    for t in range(50):
        perm = list(rng.permutation(m)) if t else list(range(m))
        pv = pivots(M, perm)
        if all(nz(p) for p in pv):
            return (sum(pos(p) for p in pv), sum(neg(p) for p in pv))
    return None
ia, ib = inertia(la), inertia(lb)
member = None
if ia and ib and abs(ia[0] - ib[0]) == 1 and abs(ia[1] - ib[1]) == 1:
    member = (min(ia[0], ib[0]), min(ia[1], ib[1]), 1)
okP = sign_change and nz(dprime) and member is not None and min(member[0], member[1]) >= 2
print(f'  C2: l* in [{float(la):.12f}, {float(lb):.12f}]; det sign change {sign_change}; det\' excludes 0 {nz(dprime)};'
      f' inertia left {ia}, right {ib} -> member {member}; index >= 2: {okP}')

# (C3) v* on the surface C_Q in a chart: c[k0] = 1, c[k1], c[k2] dyadic, 3 unknowns
cf = cf / cf[np.argmax(abs(cf))]; k0 = int(np.argmax(abs(cf)))
Jf = np.array([2 * A1 @ cf, 2 * A2 @ cf,
               [(ps(list((cf + h) @ Bm), 3) - ps(list((cf - h) @ Bm), 3)) / 2e-7
                for h in np.eye(m) * 1e-7]])
# choose the two fixed coordinates so that the remaining 3x3 block is best conditioned
cands = [k for k in range(m) if k != k0]
best3 = max(((a, b, c) for a in cands for b in cands for c in cands if a < b < c),
            key=lambda t: abs(np.linalg.det(Jf[:, list(t)])))
un2 = list(best3); fx2 = [k for k in cands if k not in un2]
cfix = {k0: mpf(1)}
for k in fx2: cfix[k] = dyad(cf[k])
def cvec(xs):
    c = [None] * m
    for k, val in cfix.items(): c[k] = iv.mpf(val)
    for i, k in enumerate(un2): c[k] = xs[i]
    return c
def qf(Mx, a, b): return sum((a[i] * Mx[i][j] * b[j] for i in range(m) for j in range(m)), iv.mpf(0))
def colk(c, k):
    v = lin(c, BI); v2 = mul(v, v)
    return [2 * sum((A1I[k][j] * c[j] for j in range(m)), iv.mpf(0)),
            2 * sum((A2I[k][j] * c[j] for j in range(m)), iv.mpf(0)), 3 * tr(mul(v2, BI[k]))]
def Fv(xs):
    c = cvec(xs); v = lin(c, BI)
    return [qf(A1I, c, c), qf(A2I, c, c), ps(v, 3)]
def Jv(xs):
    c = cvec(xs); cols = [colk(c, k) for k in un2]
    return [[cols[j][i] for j in range(3)] for i in range(3)]
cm = [mpf(float(cf[k])) for k in un2]
for it in range(40):
    Fm = [(lo(x) + hi(x)) / 2 for x in Fv([iv.mpf(x) for x in cm])]
    Jm = [[(lo(x) + hi(x)) / 2 for x in row] for row in Jv([iv.mpf(x) for x in cm])]
    dx = solve3(Jm, [-x for x in Fm]); cm = [a + b for a, b in zip(cm, dx)]
    if max(abs(x) for x in Fm) < mpf(10) ** -50: break
okC, KC = krawczyk(Fv, Jv, cm, mpf(10) ** -30, 'C3: v* on C_Q')
cI = cvec(KC); vI = lin(cI, BI)
JU = Jv(KC)
Ts = []
for kf in fx2:
    Jk = colk(cI, kf); Tun = solve3(JU, [-x for x in Jk])
    T = [iv.mpf(0)] * m; T[kf] = iv.mpf(1)
    for i, k in enumerate(un2): T[k] = Tun[i]
    Ts.append(T)
LamI = iv.mpf([la, lb])
MI = [[LamI * A1I[i][j] + A2I[i][j] for j in range(m)] for i in range(m)]
G = [[qf(MI, Ta, Tb) for Tb in Ts] for Ta in Ts]
gdet = det_g(G)
Mv = [sum((MI[i][j] * cI[j] for j in range(m)), iv.mpf(0)) for i in range(m)]
notvertex = any(nz(x) for x in Mv)
print(f'  C3: det Gram_M*(T_1..T_{kk}) in [{float(lo(gdet)):.6g}, {float(hi(gdet)):.6g}] excludes 0: {nz(gdet)}; '
      f'v* not the vertex: {notvertex}')

P4 = [ps(QI, 4)] + [comb(4, k) * tr(mul(pw(QI, 4 - k), pw(vI, k))) for k in (1, 2, 3)] + [ps(vI, 4)]
def p4at(K): return sum((P4[k] * K ** k for k in range(5)), iv.mpf(0))
def dp4at(K): return sum((k * P4[k] * K ** (k - 1) for k in range(1, 5)), iv.mpf(0))
P4m = [(lo(x) + hi(x)) / 2 for x in P4]
km = mp.findroot(lambda K: sum(P4m[k] * K ** k for k in range(5)), mpf(kf))
dk = mpf(10) ** -20; ka, kb = km - dk, km + dk
pa, pb = p4at(iv.mpf(ka)), p4at(iv.mpf(kb))
sc4 = (pos(pa) and neg(pb)) or (neg(pa) and pos(pb))
d4 = dp4at(iv.mpf([ka, kb]))
print(f'  C4: k* in [{float(ka):.12f}, {float(kb):.12f}]; p4 sign change {sc4}; p4\' excludes 0 {nz(d4)}')
allok = okQ and nz(DI) and okP and okC and nz(gdet) and notvertex and sc4 and nz(d4)
y = [float((lo(a) + hi(a)) / 2) + float(km) * float((lo(b) + hi(b)) / 2) for a, b in zip(QI, vI)]
nrm = np.linalg.norm(y); zy = zc(np.array(y))
print(f'  y = Q* + k* v*: normalised p1..p5 = {[round(np.sum(zy ** k).real / nrm ** k, 12) for k in range(1, 6)]}; '
      f'real roots of charpoly {int(sum(abs(np.roots(np.poly(zy)).imag) < 1e-7))}')
# S50.2: real coordinates of y as intervals (k over its whole interval); two of them must differ
KI = iv.mpf([ka, kb])
yI = [a + KI * b for a, b in zip(QI, vI)]
gaps = [(i, j) for i in range(r) for j in range(i) if nz(yI[i] - yI[j])]
print(f'  S50.2: real coordinates of y pairwise separated: {len(gaps)} of {r * (r - 1) // 2} pairs; '
      f'some pair differs: {len(gaps) > 0}')
print(f'CERTIFIED n = {n}, r = {r}: {allok}')
