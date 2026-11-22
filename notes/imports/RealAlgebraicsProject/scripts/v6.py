# Session 15. Needs psl_group.py (written from psl_x8.py) next to it.
# Session 15: v6 = combination of h6, k6, k6' whose iso-Hessian along Pi has even order 2 at a = b.
import cypari; pari = cypari.pari
exec(open('psl_group.py').read())
def chi(al, v): return (-1) ** bin(al & v).count('1')
a, b, y, c = pari('a'), pari('b'), pari('y'), pari('c')
def osum(mon, X):
    tot = pari(0)
    for m in orbit(mon):
        t = pari(1)
        for i, e in m: t = t * X[i]**e
        tot += t
    return tot
def rads(X):
    P = {k: sum((x**k for x in X), pari(0)) for k in (2, 3, 4, 6)}
    q = pari('41/828')*P[6] - pari('43/92')*osum({0:2,1:4}, X) - pari('13/9')*osum({0:3,1:3}, X)
    return {'h6': -69*P[2]**3 + 732*P[2]*P[4] + 736*P[3]**2 - 1440*P[6],
            'k6': osum({0:1,1:1,2:2,3:2}, X) - q, 'k6p': osum({0:1,1:1,2:2,4:2}, X) - q}
pi = [a]*4 + [b]*4 + [-4*(a + b)]
H = {}
for al in (1, 2, 3):
    e = [pari(chi(al, j)) for j in range(4)] + [pari('I')*chi(al, j) for j in range(4)] + [pari(0)]
    R = rads([pi[j] + y*e[j] for j in range(9)])
    for nm, f in R.items():
        h = pari.substpol(pari.polcoef(f, 2, y), b, a + c)
        H[(al, nm)] = h
        print(al, nm, 'val', pari.valuation(h, c), ' c^1 coeff:', pari.factor(pari.polcoef(h, 1, c)))
# solve x*k6 + z*k6p + h6 with vanishing c^1 coefficient for all chi
x, z = pari('x'), pari('z')
eqs = [pari.polcoef(H[(al,'h6')] + x*H[(al,'k6')] + z*H[(al,'k6p')], 1, c) for al in (1, 2, 3)]
for e in eqs: print(e)
print('---')
for al in (1, 2, 3):
    for nm, h in (('d6=k6-k6p', H[(al,'k6')] - H[(al,'k6p')]), ('s6=h6-414(k6+k6p)', H[(al,'h6')] - 414*(H[(al,'k6')] + H[(al,'k6p')]))):
        print(al, nm, 'val', pari.valuation(h, c), pari.factor(pari.subst(h, c, b - a)))
