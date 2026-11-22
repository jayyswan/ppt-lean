# Session 63 (S63.5): local solubility of V_K = {Tr u^3 = (Tr u)^3, Tr u^5 = (Tr u)^5} in P(K)
# at a prime p, for K = Q[x]/f (degree n; nonmonic f is made monic). Coordinates c in Z^n w.r.t.
# an integral basis of an order maximal at all primes <= pmax (PARI nfinit([f, B]); structure
# constants T and traces). V_K is homogeneous, so points of any order suffice.
# Hensel: a 2x2 minor Delta of the Jacobian with v(Delta) = m and
# v(F3), v(F5) >= 2m+1 gives a Q_p-point near c (fix the other coordinates).
# For decics (f of degree 10) use mode 'dec': W_K = {Tr u = Tr u^3 = Tr u^5 = 0} (3 equations).
# Usage: python3 loc63.py <polyname|coeffs> <pmax> [samples] [mode=non|dec] [extra primes,comma]
import sys, numpy as np, cypari
pari = cypari.pari
POLYS = {
 'psl': 'x^9 - 3*x^8 - 12000*x^7 - 295072*x^6 + 27805575*x^5 + 1157871573*x^4 + 7683210630*x^3 - 82305140040*x^2 - 848281897593*x - 1186350537195',
 's9': 'x^9 - 288*x^7 + 42*x^6 + 30219*x^5 - 10290*x^4 - 1364812*x^3 + 826728*x^2 + 22291201*x - 21772799',
 'plant': '6000*x^9 + 18000*x^8 - 38973*x^7 - 116919*x^6 + 68613*x^5 + 205839*x^4 + 6606*x^3 - 92271*x^2 - 25881*x + 1640',
}
name = sys.argv[1]
fstr = POLYS.get(name, name)
pmax = int(sys.argv[2]); S = int(sys.argv[3]) if len(sys.argv) > 3 else 20000
mode = sys.argv[4] if len(sys.argv) > 4 else 'non'
extra = [int(q) for q in sys.argv[5].split(',')] if len(sys.argv) > 5 and sys.argv[5] else []
B = max(pmax, max(extra) if extra else 0) + 1
pari.allocatemem(2*10**9)
_f = pari(fstr); _lc = int(pari.pollead(_f)); _n = int(pari.poldegree(_f))
if _lc != 1:
    fstr = str(pari('subst(%s, x, x/%d)*%d^%d' % (fstr, _lc, _lc, _n-1)))
nf = pari('nfinit([%s, %d])' % (fstr, B))      # order maximal at all primes < B
n = int(pari('poldegree(%s)' % fstr))
T = np.zeros((n, n, n), dtype=object)
for i in range(n):
    for j in range(n):
        ei = pari('vectorv(%d,k,k==%d)' % (n, i+1)); ej = pari('vectorv(%d,k,k==%d)' % (n, j+1))
        pr = pari.nfalgtobasis(nf, pari.nfeltmul(nf, ei, ej))
        for k in range(n): T[i, j, k] = int(pr[k])
trv = [int(pari.nfelttrace(nf, pari('vectorv(%d,k,k==%d)' % (n, i+1)))) for i in range(n)]
eqk = (3, 5) if mode == 'non' else (1, 3, 5)
def check_prime(p, S, rng):
    N = 1
    while p**(N+1) <= 10**8: N += 1
    M = p**N
    Tm = np.array([[[int(T[i, j, k]) % M for k in range(n)] for j in range(n)] for i in range(n)], dtype=np.int64)
    tv = np.array([x % M for x in trv], dtype=np.int64)
    C = rng.integers(0, M, size=(S, n), dtype=np.int64)
    def mul(U, V):
        R = np.zeros_like(U)
        for i in range(n):
            for j in range(n):
                uv = (U[:, i] * V[:, j]) % M
                R = (R + (uv[:, None] * Tm[i, j][None, :]) % M) % M
        return R
    def tr(V):
        out = np.zeros(V.shape[0], dtype=np.int64)
        for k in range(n): out = (out + (V[:, k] * tv[k]) % M) % M
        return out
    E = [np.tile((np.arange(n) == j).astype(np.int64), (S, 1)) for j in range(n)]
    U1 = C; U2 = mul(C, C); U3 = mul(U2, C); U4 = mul(U2, U2); U5 = mul(U4, C)
    t = tr(U1)
    def pw(a, e):
        r = np.ones_like(a)
        for _ in range(e): r = (r * a) % M
        return r
    F = {1: t, 3: (tr(U3) - pw(t, 3)) % M, 5: (tr(U5) - pw(t, 5)) % M}
    G = {}
    for k in eqk:
        Uk1 = {1: None, 3: U2, 5: U4}[k]
        cols = []
        for j in range(n):
            if k == 1:
                cols.append(np.full(S, tv[j] % M, dtype=np.int64))
            else:
                cols.append((k * ((tr(mul(Uk1, E[j])) - (pw(t, k-1) * tv[j]) % M) % M)) % M)
        G[k] = np.stack(cols, axis=1)
    def val(x):
        x = np.asarray(x, dtype=object); out = []
        for a in x:
            a = int(a) % M
            if a == 0: out.append(N); continue
            v = 0
            while a % p == 0: a //= p; v += 1
            out.append(v)
        return np.array(out)
    vF = [val(F[k]) for k in eqk]
    vFmin = np.min(np.stack(vF), axis=0)
    # nonzero projective point (some coordinate a unit)
    unit = np.any(C % p != 0, axis=1)
    cand = np.where(unit & (vFmin >= 1))[0]
    for i in cand:
        # best (smallest valuation) maximal minor of the k x n Jacobian
        J = np.array([[int(G[k][i, j]) for j in range(n)] for k in eqk], dtype=object)
        best = None
        import itertools
        for cols in itertools.combinations(range(n), len(eqk)):
            sub = [[J[r][c] for c in cols] for r in range(len(eqk))]
            if len(eqk) == 2:
                d = sub[0][0]*sub[1][1] - sub[0][1]*sub[1][0]
            else:
                d = (sub[0][0]*(sub[1][1]*sub[2][2]-sub[1][2]*sub[2][1])
                     - sub[0][1]*(sub[1][0]*sub[2][2]-sub[1][2]*sub[2][0])
                     + sub[0][2]*(sub[1][0]*sub[2][1]-sub[1][1]*sub[2][0]))
            d %= M
            if d == 0: continue
            v = 0; dd = d
            while dd % p == 0: dd //= p; v += 1
            if best is None or v < best: best = v
            if best == 0: break
        if best is not None and vFmin[i] >= 2*best + 1 and 2*best + 1 <= N:
            return True, dict(N=N, m=best, vF=[int(x[i]) for x in vF], tried=len(cand))
    return False, dict(N=N, cand=len(cand))

rng = np.random.default_rng(1)
primes = [int(q) for q in pari('primes(primepi(%d))' % pmax)] + extra
bad = []
for p in primes:
    ok, info = False, None
    for attempt in range(4):
        ok, info = check_prime(p, S, rng)
        if ok: break
    if not ok: bad.append(p)
    if (not ok) or p <= 7 or p in extra:
        print(p, 'Q_p-point' if ok else 'NOT FOUND', info, flush=True)
print('primes checked:', len(primes), ' not found:', bad)
