# Session 15. Needs psl_group.py (written from psl_x8.py) next to it.
# Session 15: PSL(2,8)-invariants g of degree d vanishing to order >= 6 at x8 = (1^8,-8),
# with sextic cone F6 nonzero at the isotropic V4-eigenvectors e = e_chi + i e'_chi.
# usage: python3 ord6.py d [m]   (m = target order, default 6)
import sys, itertools, collections, random
import cypari
pari = cypari.pari
pari.allocatemem(2*10**9)
exec(open('psl_group.py').read())
d = int(sys.argv[1]); m = int(sys.argv[2]) if len(sys.argv) > 2 else 6
def monomials(d, n=9):
    for c in itertools.combinations_with_replacement(range(n), d):
        yield tuple(sorted(collections.Counter(c).items()))
seen, orbs = set(), []
for mo in monomials(d):
    if mo in seen: continue
    o = sorted({tuple(sorted((g[i], e) for i, e in mo)) for g in G}); seen |= set(o); orbs.append(o)
print('degree', d, 'orbits', len(orbs), flush=True)
pari('default(seriesprecision,%d)' % (m + 1))
x8 = [1]*8 + [-8]
def taylor(v):
    # v: list of 9 PARI-parsable strings (trace zero). Returns list over orbits of [coef eps^0..eps^m]
    X = [pari('(%d) + (%s)*E + O(E^%d)' % (x8[j], v[j], m + 1)) for j in range(9)]
    POW = [[pari(1)] for _ in range(9)]
    for j in range(9):
        for e in range(1, d + 1): POW[j].append(POW[j][-1] * X[j])
    out = []
    for o in orbs:
        tot = pari(0)
        for mo in o:
            t = pari(1)
            for i, e in mo: t = t * POW[i][e]
            tot += t
        out.append([pari.polcoef(tot, k, pari('E')) for k in range(m + 1)])
    return out
rnd = random.Random(5)
rows = []
nconds = 0
for r in range(14):
    v = [rnd.randint(-30, 30) for _ in range(8)]; v.append(-sum(v))
    T = taylor([str(z) for z in v])
    for k in range(m):
        rows.append([T[j][k] for j in range(len(orbs))])
M = pari.matrix(len(rows), len(orbs), [c for row in rows for c in row])
K = pari.matker(M)
print('kernel dim (order >= %d at x8, incl. multiples of p1):' % m, pari.matsize(K)[1], flush=True)
def chi(al, v): return (-1) ** bin(al & v).count('1')
res = {}
for al in (1, 2, 3):
    for sg in ('I', '-I'):
        e = [str(chi(al, j)) for j in range(4)] + ['(%s)*(%d)' % (sg, chi(al, j)) for j in range(4)] + ['0']
        T = taylor(e)
        res[(al, sg)] = [T[j][m] for j in range(len(orbs))]
ncol = int(pari.matsize(K)[1])
vals = [[sum((res[key][j] * K[j, c] for j in range(len(orbs))), pari(0)) for key in sorted(res)] for c in range(ncol)]
print('F_%d at the six isotropic eigenvectors, per kernel vector:' % m)
for c in range(ncol): print('  ', [str(z) for z in vals[c]])
import pickle; pickle.dump(([o for o in orbs], [[str(K[j, c]) for j in range(len(orbs))] for c in range(ncol)], [[str(z) for z in vv] for vv in vals]), open('ord6_%d_%d.pkl' % (d, m), 'wb'))
