# parts68.py -- session 68 (S68.2, S68.4): factor-degree types of degree-10 etale algebras.
# (a) which partitions of 10 have a sub-multiset summing to 5 (a rational node, d = 1);
# (b) the p-field types (all factor degrees p-powers) and what covers each;
# (c) the leading-term system for type (3,3,3,1) with traces k = 1, 3, 5 (exact).
# Usage: python3 parts68.py
from itertools import combinations
from sympy.utilities.iterables import partitions
import cypari; pari = cypari.pari

def has5(lam):
    return any(sum(c) == 5 for r in range(1, len(lam)+1) for c in combinations(lam, r))

P10 = [sorted([k for k, m in p.items() for _ in range(m)], reverse=True) for p in partitions(10)]
nonode = [l for l in P10 if not has5(l)]
print("partitions of 10:", len(P10), " without a 5-subset (no split node):", len(nonode))
print("  ", nonode)
# nonic types: A = K x Q, i.e. partitions of 10 containing a 1 (the zeta factor)
nonic = [l for l in P10 if 1 in l]
print("nonic-type partitions (contain a 1):", len(nonic), " without a 5-subset:",
      [l for l in nonic if not has5(l)])

def ppow(d, p):
    while d % p == 0: d //= p
    return d == 1
for p in (2, 3, 5, 7, 11):
    T = [l for l in P10 if all(ppow(d, p) for d in l)]
    print("p =", p, "types:", T, " no-node:", [l for l in T if not has5(l)])

# (c) leading constants y1,y2,y3 (cubic factors, weight 3) and y4 (the F factor):
#  3(y1+y2+y3) + y4 = 0, 3 sum y^3 + y4^3 = 0, 3 sum y^5 + y4^5 = 0.
# Branch S = y1+y2+y3 = 1: e1 = 1, p3 = 9, p5 = 81 -> cubic with roots y1,y2,y3.
e2, e3 = pari('e2'), pari('e3')
p3 = 1 - 3*e2 + 3*e3; p5 = 1 - 5*e2 + 5*e2**2 + 5*e3 - 5*e2*e3
print("Newton check p3, p5:", p3, "|", p5)
sol = pari('solve_e = 0')  # placeholder
E2 = pari('-5'); E3 = pari('-7/3')
print("p3(e2=-5,e3=-7/3) =", pari.subst(pari.subst(p3, 'e2', E2), 'e3', E3),
      " p5 =", pari.subst(pari.subst(p5, 'e2', E2), 'e3', E3))
cub = pari('3*x^3 - 3*x^2 - 15*x + 7')
print("cubic 3x^3-3x^2-15x+7: irreducible =", pari.polisirreducible(cub),
      " disc =", pari.poldisc(cub), " factored:", pari.factor(pari.poldisc(cub)),
      " Galois group:", pari.polgalois(cub))
