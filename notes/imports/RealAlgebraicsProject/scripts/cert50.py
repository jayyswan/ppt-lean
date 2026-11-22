# Session 50: P-conics in V_3 through two P-points for DECICS (n = 10), A_10 r = 6 (s = 2).
# Usage: python3 cert50.py <r> <seed> [maxattempts] [n]   (default n = 10; self-contained; writes nothing)
#
# Conics q(k) = Q1 + k u + k^2 s Q2 in V_3 through Q1, Q2 in V_3 (S46.1 notation):
#   u in L = {Tr u = Tr Q1u = Tr Q2u = Tr Q1^2u = Tr Q2^2u = 0} (dim n - 5; P(L) = P^4 for n = 10),
#   N1 = Tr((a - 2mQ1)U^2), N2 = Tr((b - 2mQ2)U^2) (pencil), F3 = m Tr(u^3) - 3 Tr(u^2) Tr(Q1Q2u) (cubic),
#   s = -Tr(u^2)/(2m), with m = Tr(Q1Q2), a = Tr(Q1^2Q2), b = Tr(Q1Q2^2).
# For n = 10 the conics through Q1, Q2 form the (2,2,3) curve C in P^4: a curve on a quartic del Pezzo,
# exactly the S48.1 structure. Certified open real conditions (mpmath.iv, 60 digits, Krawczyk):
#  (D1) Q1*, Q2* real points of V_3 where V_3 is smooth; the 5 linear conditions defining L independent;
#  (D2) a simple real root l* of det(l N1 + N2) (degree 5) whose member has inertia (2,2,1);
#  (D3) a real point u* of C, smooth (Krawczyk in a chart), not the vertex, with M*(T,T) != 0;
#  (D4) s* != 0 and a simple real root k* of p4(q(k)) (degree 8).
import sys, numpy as np
from mpmath import mp, iv, mpf
from math import comb
from itertools import combinations

n = int(sys.argv[4]) if len(sys.argv) > 4 else 10
r = int(sys.argv[1]); seed = int(sys.argv[2]); s_ = (n - r) // 2
maxatt = int(sys.argv[3]) if len(sys.argv) > 3 else 200
dL = n - 5
rng = np.random.default_rng(seed)
mp.dps = 60; iv.dps = 60
lo = lambda x: mpf(x.a); hi = lambda x: mpf(x.b)
def pos(x): return lo(x) > 0
def neg(x): return hi(x) < 0
def nz(x): return pos(x) or neg(x)
def mid(x): return (lo(x) + hi(x)) / 2

def mul(u, w):
    out = [u[i] * w[i] for i in range(r)]
    for j in range(s_):
        a, b = u[r + 2 * j], u[r + 2 * j + 1]; c, d = w[r + 2 * j], w[r + 2 * j + 1]
        out += [a * c - b * d, a * d + b * c]
    return out
def tr(u):
    t = u[0]
    for i in range(1, r): t = t + u[i]
    for j in range(s_): t = t + 2 * u[r + 2 * j]
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
def add(u, w): return [x + y for x, y in zip(u, w)]
def scl(c, u): return [c * x for x in u]

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

# ---------- generic small linear algebra (works for floats, mpf and iv.mpf) ----------
def gsolve(M, b):
    k = len(M); A = [list(M[i]) + [b[i]] for i in range(k)]
    for c in range(k):
        for i in range(c + 1, k):
            f = A[i][c] / A[c][c]
            for j in range(c, k + 1): A[i][j] = A[i][j] - f * A[c][j]
    x = [None] * k
    for i in reversed(range(k)):
        t = A[i][k]
        for j in range(i + 1, k): t = t - A[i][j] * x[j]
        x[i] = t / A[i][i]
    return x
def det_g(M):
    M = [list(row) for row in M]; k = len(M); d = None
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

def trow(w, one):
    # row of the functional u -> Tr(w u) in real coordinates
    row = [w[i] for i in range(r)]
    for j in range(s_): row += [2 * w[r + 2 * j], -2 * w[r + 2 * j + 1]]
    return row
def L_basis(Q1, Q2, piv, one, zero):
    ws = [[one] * r + sum([[one, zero] for _ in range(s_)], []), Q1, Q2, mul(Q1, Q1), mul(Q2, Q2)]
    rows = [trow(w, one) for w in ws]
    Pv, Fv = piv
    MP = [[rows[k][p] for p in Pv] for k in range(5)]
    basis = []
    for f in Fv:
        rhs = [-rows[k][f] for k in range(5)]
        x = gsolve(MP, rhs)
        v = [zero] * n; v[f] = one
        for c in range(5): v[Pv[c]] = x[c]
        basis.append(v)
    return basis, det_g(MP)

def setup(Q1, Q2, B):
    m = tr(mul(Q1, Q2)); a = tr(mul(mul(Q1, Q1), Q2)); b = tr(mul(Q1, mul(Q2, Q2)))
    W1 = add(scl(a, one_vec(Q1)), scl(-2 * m, Q1))
    W2 = add(scl(b, one_vec(Q1)), scl(-2 * m, Q2))
    k = len(B); prod = [[mul(B[i], B[j]) for j in range(k)] for i in range(k)]
    N1 = [[tr(mul(W1, prod[i][j])) for j in range(k)] for i in range(k)]
    N2 = [[tr(mul(W2, prod[i][j])) for j in range(k)] for i in range(k)]
    return m, a, b, N1, N2
def one_vec(Q):
    one = Q[0] * 0 + 1; zero = Q[0] * 0
    return [one] * r + sum([[one, zero] for _ in range(s_)], [])

def F3val(u, Q12, m):
    u2 = mul(u, u)
    return m * tr(mul(u2, u)) - 3 * tr(u2) * tr(mul(Q12, u))

def p4_conic(Q1, Q2, u, sv):
    # coefficients (k^0..k^8) of p_j(Q1 + k u + k^2 s Q2) for j = 1..4
    q = [Q1, u, scl(sv, Q2)]
    def pmul(P, R):
        out = [None] * (len(P) + len(R) - 1)
        for i, x in enumerate(P):
            for j, y in enumerate(R):
                t = mul(x, y); out[i + j] = t if out[i + j] is None else add(out[i + j], t)
        return out
    q2 = pmul(q, q); q3 = pmul(q2, q); q4 = pmul(q2, q2)
    return [[tr(c) for c in P] for P in (q, q2, q3, q4)]

# ===================== float stage =====================
stats = dict(pairs=0, pencil=0, C=0, s_pos=0, p4real=0, unram=0)
found = None
for attempt in range(maxatt):
    Q1 = v3_point(); Q2 = v3_point(); stats['pairs'] += 1
    if tr(mul(list(Q1), list(Q2))) > 0: Q2 = -Q2          # -Q2 is also in V_3; Lemma C wants m < 0
    rows = np.array([trow(w, 1.0) for w in
                     [[1.0] * r + [1.0, 0.0] * s_, list(Q1), list(Q2), mul(list(Q1), list(Q1)), mul(list(Q2), list(Q2))]])

    Pv = list(max(combinations(range(n), 5), key=lambda t: abs(np.linalg.det(rows[:, list(t)]))))
    Fv = [j for j in range(n) if j not in Pv]
    B, _ = L_basis(list(Q1), list(Q2), (Pv, Fv), 1.0, 0.0); Bm = np.array(B)
    m, a, b, N1, N2 = setup(list(Q1), list(Q2), B); N1 = np.array(N1); N2 = np.array(N2)
    Q12 = mul(list(Q1), list(Q2))
    ls = np.linspace(-3, 3, 13)
    co = np.polyfit(ls, [np.linalg.det(l * N1 + N2) for l in ls], dL)
    cand = []
    for x in np.roots(co):
        if abs(x.imag) < 1e-9:
            ev = np.linalg.eigvalsh(x.real * N1 + N2); ev = ev[np.argsort(abs(ev))][1:]
            if (ev > 0).sum() == 2 and (ev < 0).sum() == 2: cand.append(x.real)
    if not cand: continue
    stats['pencil'] += 1
    def F3c(c): return F3val(list(c @ Bm), Q12, m)
    def Fc(c): return np.array([c @ N1 @ c, c @ N2 @ c, F3c(c), c @ c - 1])
    def Jc(c):
        g = np.zeros(dL); h = 1e-7
        for i in range(dL):
            e = np.zeros(dL); e[i] = h; g[i] = (F3c(c + e) - F3c(c - e)) / (2 * h)
        return np.vstack([2 * N1 @ c, 2 * N2 @ c, g, 2 * c])
    for lam in cand:
        Mst = lam * N1 + N2
        for st in range(120):
            c = rng.normal(size=dL); c /= np.linalg.norm(c)
            for it in range(60):
                F = Fc(c); c = c + np.linalg.lstsq(Jc(c), -F, rcond=None)[0]
                if not np.isfinite(c).all() or np.linalg.norm(F) < 1e-13: break
            if not np.isfinite(c).all() or np.linalg.norm(Fc(c)) > 1e-11: continue
            stats['C'] += 1
            u = c @ Bm; sv = -tr(mul(list(u), list(u))) / (2 * m)
            if sv > 0: stats['s_pos'] += 1
            P = p4_conic(list(Q1), list(Q2), list(u), sv)
            assert max(abs(x) for x in P[0] + P[1] + P[2]) < 1e-8, 'conic not in V_3'
            rts = [x.real for x in np.roots(P[3][::-1]) if abs(x.imag) < 1e-9]
            if not rts: continue
            stats['p4real'] += 1
            Tn = np.linalg.svd(np.vstack([Jc(c)[:3], c]))[2][4:]
            MT = abs(Tn[0] @ Mst @ Tn[0]) / np.linalg.norm(Mst, 2)
            if MT < 1e-3 or np.linalg.norm(Mst @ c) / np.linalg.norm(Mst, 2) < 1e-3: continue
            stats['unram'] += 1
            dq = np.polyder(np.poly1d(P[3][::-1]))
            k0 = max(rts, key=lambda k: abs(dq(k)) / (1 + abs(k)) ** 7)
            found = (Q1, Q2, lam, c, k0, Pv, Fv); break
        if found: break
    if found: break
print(f'n = {n}, r = {r}, seed {seed}: float stats {stats}')
if not found:
    print(f'no float sample in {maxatt} attempts'); print(f'CERTIFIED n = {n}, r = {r}: False'); sys.exit()
Q1f, Q2f, lam, cf, kf, Pv, Fv = found
print(f'float sample at attempt {attempt}; m = {tr(mul(list(Q1f), list(Q2f))):.5f}; l* ~ {lam:.6f}; k* ~ {kf:.6f}')

# ===================== rigorous stage =====================
ONE, ZERO = iv.mpf(1), iv.mpf(0)
D60 = mpf(2) ** -60
def dyad(x): return mpf(int(round(x / float(D60)))) * D60
def F3p(u): return [ps(u, 1), ps(u, 2), ps(u, 3)]
def J3p(u, unk):
    out = []
    for k in (1, 2, 3):
        uk = pw(u, k - 1) if k > 1 else None
        row = []
        for j in unk:
            e = [(ONE if i == j else ZERO) for i in range(n)] if isinstance(u[0], iv.mpf) else \
                [(mpf(1) if i == j else mpf(0)) for i in range(n)]
            row.append(k * tr(mul(uk, e)) if k > 1 else tr(e))
        out.append(row)
    return out

def krawczyk(Fun, Jac, xm, rad, label):
    k = len(xm)
    X = [iv.mpf([xm[i] - rad, xm[i] + rad]) for i in range(k)]
    Jm = Jac([iv.mpf(x) for x in xm])
    Jmid = mp.matrix([[mid(Jm[i][j]) for j in range(k)] for i in range(k)])
    Y = Jmid ** -1
    Fx = Fun([iv.mpf(x) for x in xm]); JX = Jac(X)
    K = []
    for i in range(k):
        t = iv.mpf(xm[i])
        for a_ in range(k): t = t - iv.mpf(Y[i, a_]) * Fx[a_]
        for j in range(k):
            bb = (iv.mpf(1) if i == j else iv.mpf(0))
            for a_ in range(k): bb = bb - iv.mpf(Y[i, a_]) * JX[a_][j]
            t = t + bb * (X[j] - iv.mpf(xm[j]))
        K.append(t)
    ok = all(lo(K[i]) > lo(X[i]) and hi(K[i]) < hi(X[i]) for i in range(k))
    print(f'  Krawczyk [{label}]: n = {k}, radius {float(rad):.1e}: K(X) in int(X) = {ok}')
    return ok, K

def certify_point(Qf, label):
    J = jac3(Qf)
    unk = list(max(combinations(range(n), 3), key=lambda t: abs(np.linalg.det(J[:, list(t)]))))
    Qm = [dyad(x) for x in Qf]
    for it in range(40):
        Fm = F3p(Qm); dx = gsolve(J3p(Qm, unk), [-x for x in Fm])
        for c, j in enumerate(unk): Qm[j] += dx[c]
        if max(abs(x) for x in Fm) < mpf(10) ** -55: break
    def box(xs):
        u = [iv.mpf(Qm[j]) for j in range(n)]
        for c, j in enumerate(unk): u[j] = xs[c]
        return u
    ok, K = krawczyk(lambda xs: F3p(box(xs)), lambda xs: J3p(box(xs), unk), [Qm[j] for j in unk],
                     mpf(10) ** -40, label)
    return ok, box(K)
ok1, Q1I = certify_point(Q1f, 'D1: Q1* on V_3')
ok2, Q2I = certify_point(Q2f, 'D1: Q2* on V_3')
BI, DI = L_basis(Q1I, Q2I, (Pv, Fv), ONE, ZERO)
mI, aI, bI, N1I, N2I = setup(Q1I, Q2I, BI)
Q12I = mul(Q1I, Q2I)
print(f'  L: pivot determinant excludes 0: {nz(DI)}; m in [{float(lo(mI)):.6f}, {float(hi(mI)):.6f}], m < 0: {neg(mI)}')

def detI(l):
    lI = iv.mpf(l) if not isinstance(l, iv.mpf) else l
    return det_g([[lI * N1I[i][j] + N2I[i][j] for j in range(dL)] for i in range(dL)])
lm = mp.findroot(lambda l: mid(detI(iv.mpf(l))), mpf(lam))
dl = mpf(10) ** -25; la, lb = lm - dl, lm + dl
da, db = detI(la), detI(lb)
sign_change = (pos(da) and neg(db)) or (neg(da) and pos(db))
nodes = list(range(-3, dL - 2))
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
    M = [[iv.mpf(l) * N1I[i][j] + N2I[i][j] for j in range(dL)] for i in range(dL)]
    for t in range(50):
        perm = list(rng.permutation(dL)) if t else list(range(dL))
        pv = pivots(M, perm)
        if all(nz(p) for p in pv): return (sum(pos(p) for p in pv), sum(neg(p) for p in pv))
    return None
ia, ib = inertia(la), inertia(lb)
member = None
if ia and ib and abs(ia[0] - ib[0]) == 1 and abs(ia[1] - ib[1]) == 1:
    member = (min(ia[0], ib[0]), min(ia[1], ib[1]), 1)
okP = sign_change and nz(dprime) and member == (2, 2, 1)
print(f"  D2: l* in [{float(la):.12f}, {float(lb):.12f}]; det sign change {sign_change}; det' excludes 0 {nz(dprime)};"
      f' inertia left {ia}, right {ib} -> member {member}; (2,2,1): {okP}')

# D3: u* on C in a chart: c[k0] = 1, one more coordinate fixed (dyadic), 3 unknowns
cf = cf / cf[np.argmax(abs(cf))]; k0 = int(np.argmax(abs(cf)))
Bm_f = np.array([[float(mid(x)) for x in row] for row in BI])
def F3f(c): return F3val(list(c @ Bm_f), [float(mid(x)) for x in Q12I], float(mid(mI)))
N1f = np.array([[float(mid(x)) for x in row] for row in N1I]); N2f = np.array([[float(mid(x)) for x in row] for row in N2I])
Jf = np.array([2 * N1f @ cf, 2 * N2f @ cf, [(F3f(cf + h) - F3f(cf - h)) / 2e-7 for h in np.eye(dL) * 1e-7]])
cands = [k for k in range(dL) if k != k0]
un2 = list(max(combinations(cands, 3), key=lambda t: abs(np.linalg.det(Jf[:, list(t)]))))
fx2 = [k for k in cands if k not in un2]
cfix = {k0: mpf(1)}
for k in fx2: cfix[k] = dyad(cf[k])
def cvec(xs):
    c = [None] * dL
    for k, val in cfix.items(): c[k] = iv.mpf(val)
    for i, k in enumerate(un2): c[k] = xs[i]
    return c
def qf(Mx, x, y): return sum((x[i] * Mx[i][j] * y[j] for i in range(dL) for j in range(dL)), iv.mpf(0))
def colk(c, k):
    u = lin(c, BI); u2 = mul(u, u); t12 = tr(mul(Q12I, u))
    dF = 3 * mI * tr(mul(u2, BI[k])) - 3 * (2 * tr(mul(u, BI[k])) * t12 + tr(u2) * tr(mul(Q12I, BI[k])))
    return [2 * sum((N1I[k][j] * c[j] for j in range(dL)), iv.mpf(0)),
            2 * sum((N2I[k][j] * c[j] for j in range(dL)), iv.mpf(0)), dF]
def Fv_(xs):
    c = cvec(xs); u = lin(c, BI)
    return [qf(N1I, c, c), qf(N2I, c, c), F3val(u, Q12I, mI)]
def Jv_(xs):
    c = cvec(xs); cols = [colk(c, k) for k in un2]
    return [[cols[j][i] for j in range(3)] for i in range(3)]
cm = [mpf(float(cf[k])) for k in un2]
for it in range(40):
    Fm = [mid(x) for x in Fv_([iv.mpf(x) for x in cm])]
    Jm = [[mid(x) for x in row] for row in Jv_([iv.mpf(x) for x in cm])]
    dx = gsolve(Jm, [-x for x in Fm]); cm = [x + y for x, y in zip(cm, dx)]
    if max(abs(x) for x in Fm) < mpf(10) ** -50: break
okC, KC = krawczyk(Fv_, Jv_, cm, mpf(10) ** -30, 'D3: u* on C')
cI = cvec(KC); uI = lin(cI, BI)
JU = Jv_(KC); kf2 = fx2[0]
Tun = gsolve(JU, [-x for x in colk(cI, kf2)])
T = [iv.mpf(0)] * dL; T[kf2] = iv.mpf(1)
for i, k in enumerate(un2): T[k] = Tun[i]
LamI = iv.mpf([la, lb])
MI = [[LamI * N1I[i][j] + N2I[i][j] for j in range(dL)] for i in range(dL)]
MTT = qf(MI, T, T)
Mu = [sum((MI[i][j] * cI[j] for j in range(dL)), iv.mpf(0)) for i in range(dL)]
notvertex = any(nz(x) for x in Mu)
print(f'  D3: M*(T,T) in [{float(lo(MTT)):.6g}, {float(hi(MTT)):.6g}] excludes 0: {nz(MTT)}; u* not the vertex: {notvertex}')

# D4: s and p4 on the conic
sI = -tr(mul(uI, uI)) / (2 * mI)
P = p4_conic(Q1I, Q2I, uI, sI)
inV3 = all(lo(x) <= 0 <= hi(x) for x in P[0] + P[1] + P[2])
def p4at(K): return sum((P[3][k] * K ** k for k in range(9)), iv.mpf(0))
def dp4at(K): return sum((k * P[3][k] * K ** (k - 1) for k in range(1, 9)), iv.mpf(0))
P4m = [mid(x) for x in P[3]]
km = mp.findroot(lambda K: sum(P4m[k] * K ** k for k in range(9)), mpf(kf))
dk = mpf(10) ** -20; ka, kb = km - dk, km + dk
pa, pb = p4at(iv.mpf(ka)), p4at(iv.mpf(kb))
sc4 = (pos(pa) and neg(pb)) or (neg(pa) and pos(pb))
d4 = dp4at(iv.mpf([ka, kb]))
print(f'  D4: s in [{float(lo(sI)):.6g}, {float(hi(sI)):.6g}] excludes 0: {nz(sI)}; p1,p2,p3 coefficients enclose 0: {inV3}; '
      f"k* in [{float(ka):.12f}, {float(kb):.12f}]; p4 sign change {sc4}; p4' excludes 0 {nz(d4)}")
allok = ok1 and ok2 and nz(DI) and okP and okC and nz(MTT) and notvertex and nz(sI) and sc4 and nz(d4)
y = [float(mid(q1) + km * mid(uu) + km ** 2 * mid(sI) * mid(q2)) for q1, uu, q2 in zip(Q1I, uI, Q2I)]
nrm = np.linalg.norm(y); zy = zc(np.array(y))
print(f'  y = q(k*): normalised p1..p5 = {[round(np.sum(zy ** k).real / nrm ** k, 12) for k in range(1, 6)]}; '
      f'real roots of charpoly {int(sum(abs(np.roots(np.poly(zy)).imag) < 1e-7))}')
# S50.2: for the padded algebra K x P (nonic K, r = 5) both complex factors belong to K: their imaginary parts
# must be nonzero, so the K-part of y is not in P
KI = iv.mpf([ka, kb])
yI = [q1 + KI * uu + KI ** 2 * sI * q2 for q1, uu, q2 in zip(Q1I, uI, Q2I)]
imz = [nz(yI[r + 2 * j + 1]) for j in range(s_)]
print(f'  S50.2: imaginary parts of the complex coordinates of y exclude 0: {imz}')
print(f'CERTIFIED n = {n}, r = {r}: {allok}')
