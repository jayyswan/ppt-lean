# Session 17: check the r = 1 test nonic has group PSL(2,8) (9T27) and one real root.
import collections, cypari
pari = cypari.pari
f = pari('x^9 - 3*x^8 + 12*x^6 - 14*x^5 - 2*x^4 + 12*x^2 + x + 1')
print('irreducible', pari.polisirreducible(f), ' real roots', pari.polsturm(f))
D = pari.poldisc(f); print('disc', D, ' square:', pari('issquare')(D), pari.factor(D))
allowed = {(1,)*9, (1,2,2,2,2), (3,3,3), (1,1,7), (9,)}
ct = collections.Counter()
for p in pari.primes(5000):
    p = int(p)
    if D % p == 0: continue
    fp = pari.factormod(f, p)
    degs = tuple(sorted(int(pari.poldegree(pari.lift(g))) for g in fp[0]))
    ct[degs] += 1
print(dict(ct)); print('all types in PSL(2,8):', set(ct) <= allowed)
# PSL(2,8) class proportions on 9 points: 1/504, 63/504 (2^4), 56+... compute exactly below
