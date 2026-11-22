"""Session 11: line test (Q4 on y = u + t v) and plane test (D = {Q4 = Q5 = 0} on span(u, v, w))
with the non-symmetric PSL(2,8)-covariants of degree 4 from cov4.py, at random rational x.
Quartic groups via PARI polgalois; degree-20 polynomials written to files for frob_group.py."""
import random, itertools, collections, cypari
from fractions import Fraction
from psl28 import covariant_orbits, covariant
pari = cypari.pari
orbs = covariant_orbits(4); new = {'c4': orbs[4], 'c5': orbs[5], 'c9': orbs[9]}
def pw(x, k): return sum(v**k for v in x)
def proj(v): m = sum(v) / len(v); return [a - m for a in v]
def Q4(y): return 6*pw(y, 4) - pw(y, 2)**2
def Q5(y): return 18*pw(y, 5) - 5*pw(y, 2)*pw(y, 3)
rnd = random.Random(31)
def sample():
    while True:
        x = [rnd.randint(-15, 15) for _ in range(9)]
        if len(set(x)) == 9: break
    x = proj([Fraction(v) for v in x]); x = [v * 9 for v in x]
    c = {'s1': x, 's2': proj([v**2 for v in x]), 's3': proj([v**3 for v in x])}
    for k, o in new.items(): c[k] = proj(covariant(o, x))
    return {k: [pari(str(a)) for a in v] for k, v in c.items()}

T = pari('t')
pairs = [('s1', 'c4'), ('s1', 'c5'), ('s1', 'c9'), ('s2', 'c4'), ('s2', 'c9'),
         ('c4', 'c5'), ('c4', 'c9'), ('c5', 'c9')]
stats = collections.defaultdict(collections.Counter)
samples = [sample() for _ in range(30)]
for c in samples:
    for u, v in pairs:
        q = Q4([a + T*b for a, b in zip(c[u], c[v])])
        if pari.polisirreducible(q):
            gname = str(pari.polgalois(q)[3])
        else:
            gname = 'reducible ' + str([int(pari.poldegree(f)) for f in pari.factor(q)[0]])
        stats[(u, v)][gname] += 1
print('Q4 on lines u + t v, 30 random rational x:')
for k, v in stats.items(): print('  ', k, dict(v))

A, B = pari('a'), pari('b')
planes = [('s1', 's2', 'c4'), ('s1', 's2', 'c9'), ('s1', 'c4', 'c9'), ('c4', 'c5', 'c9')]
for n, c in enumerate(samples[:2]):
    for P in planes:
        y = [A*a + B*b + z for a, b, z in zip(c[P[0]], c[P[1]], c[P[2]])]
        R = pari.polresultant(Q4(y), Q5(y), B); R = R / pari.content(R)
        fa = pari.factor(R); degs = [int(pari.poldegree(f)) for f in fa[0]]
        print('plane', P, 'sample', n, 'factor degrees', degs)
        open('plane_%s_%d.pol' % ('_'.join(P), n), 'w').write(str(fa[0][degs.index(max(degs))]))
