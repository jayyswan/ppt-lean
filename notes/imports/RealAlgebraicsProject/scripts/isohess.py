# Session 15. Needs psl_group.py (written from psl_x8.py) next to it.
# Session 15: PSL(2,8)-invariants f of degree d vanishing on Pi whose "iso-Hessian"
# H_f(e)(a,b) = [y^2] f(pi(a,b) + y e),  e = e_chi + i e'_chi  (isotropic V4-eigenvector),
# has even order (exactly 2) in (a - b) at a = b, for all three chi.
# Symmetric f always give odd order there (H(e)(a,b) = -H(e)(b,a)).
# usage: python3 isohess.py d
import sys, itertools, collections, pickle
import cypari
pari = cypari.pari
pari.allocatemem(2*10**9)
exec(open('psl_group.py').read())
d = int(sys.argv[1])
def monomials(d, n=9):
    for c in itertools.combinations_with_replacement(range(n), d):
        yield tuple(sorted(collections.Counter(c).items()))
seen, orbs = set(), []
for mo in monomials(d):
    if mo in seen: continue
    o = sorted({tuple(sorted((g[i], e) for i, e in mo)) for g in G}); seen |= set(o); orbs.append(o)
print('degree', d, 'orbits', len(orbs), flush=True)
def chi(al, v): return (-1) ** bin(al & v).count('1')
a, b, y = pari('a'), pari('b'), pari('y')
def osums(X, trunc_y=None):
    POW = [[pari(1)] for _ in range(9)]
    for j in range(9):
        for e in range(1, d + 1):
            t = POW[j][-1] * X[j]
            if trunc_y is not None: t = t + pari('O(y^%d)' % (trunc_y + 1))
            POW[j].append(t)
    out = []
    for o in orbs:
        tot = pari(0)
        for mo in o:
            t = pari(1)
            for i, e in mo: t = t * POW[i][e]
            tot += t
        out.append(tot)
    return out
pi = [a]*4 + [b]*4 + [-4*(a + b)]
onPi = osums(pi)
# linear conditions: all coefficients of the binary form
rows = []
for k in range(d + 1):
    rows.append([pari.polcoef(pari.polcoef(f, k, a), d - k, b) for f in onPi])
M = pari.matrix(len(rows), len(orbs), [c for r in rows for c in r])
K = pari.matker(M); nk = int(pari.matsize(K)[1])
print('Pi-vanishing (incl. p1 multiples):', nk, flush=True)
H = {}
for al in (1, 2, 3):
    e = [pari(chi(al, j)) for j in range(4)] + [pari('I') * chi(al, j) for j in range(4)] + [pari(0)]
    X = [pi[j] + y * e[j] for j in range(9)]
    S = osums(X)
    H[al] = [pari.polcoef(s, 2, y) for s in S]
    H1 = [pari.polcoef(s, 1, y) for s in S]
# for each kernel vector, H as binary form; reduce to substitution b = a + c, order in c
c = pari('c')
def hk(al, col):
    h = sum((H[al][j] * K[j, col] for j in range(len(orbs))), pari(0))
    return pari.substpol(h, b, a + c) if h != 0 else h
# matrix of coefficients of c^0 and c^1 (at a = 1) for all chi, Re and Im
rows2, rows3 = [], []
for al in (1, 2, 3):
    for k in (0, 1):
        r = [pari.polcoef(pari.subst(hk(al, col), a, 1), k, c) if hk(al, col) != 0 else pari(0) for col in range(nk)]
        rows2.append([pari.real(z) for z in r]); rows2.append([pari.imag(z) for z in r])
M2 = pari.matrix(len(rows2), nk, [z for r in rows2 for z in r])
K2 = pari.matker(M2); n2 = int(pari.matsize(K2)[1])
print('iso-Hessians of order >= 2 at a = b, all chi:', n2, flush=True)
good = []
for col in range(n2):
    vec = K * K2[:, col] if False else pari.matmultodiag if False else None
KK = K * K2
for col in range(n2):
    orders = []
    for al in (1, 2, 3):
        h = sum((H[al][j] * KK[j, col] for j in range(len(orbs))), pari(0))
        if h == 0: orders.append(None); continue
        h = pari.substpol(h, b, a + c)
        orders.append(int(pari.valuation(h, c)))
    print('  vector', col, 'orders at a=b per chi:', orders)
    good.append(([str(KK[j, col]) for j in range(len(orbs))], orders))
pickle.dump((orbs, good), open('isohess_%d.pkl' % d, 'wb'))
