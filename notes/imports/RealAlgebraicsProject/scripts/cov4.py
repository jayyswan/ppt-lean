"""Session 11: explicit PSL(2,8)-covariants V -> V of degree 4 that are not symmetric.
Spans the G_inf-orbit covariants of degree 4, projects to V, restricts to trace-zero x, and
removes the symmetric ones ((s^4)', p2 (s^2)', p3 s'). Checks equivariance numerically.
Writes cov4.txt: a basis of new covariants as lists of G_inf-orbits of monomials with
rational weights (orbit representatives)."""
import random, itertools
from fractions import Fraction
import sympy as sp
from psl28 import G, INF, covariant_orbits, covariant, act

orbs = covariant_orbits(4)
rnd = random.Random(5)
def rand_tz():
    x = [Fraction(rnd.randint(-30, 30)) for _ in range(9)]
    m = sum(x) / 9
    return [v - m for v in x]
def proj(v):
    m = sum(v) / 9; return [a - m for a in v]
def pw(x, k): return sum(v**k for v in x)

# sample points; each covariant gives a vector in Q^9 per sample -> stack
pts = [rand_tz() for _ in range(40)]
def vec(cfun):
    out = []
    for x in pts: out += proj(cfun(x))
    return out
cols = [vec(lambda x, o=o: covariant(o, x)) for o in orbs]
sym = [vec(lambda x: [v**4 for v in x]),
       vec(lambda x: [pw(x, 2) * v**2 for v in x]),
       vec(lambda x: [pw(x, 3) * v for v in x])]
M = sp.Matrix(cols).T
print('rank of all degree-4 covariants on V:', M.rank())
print('rank of symmetric ones:', sp.Matrix(sym).T.rank())
print('rank symmetric + all:', sp.Matrix(sym + cols).T.rank())
# choose new basis: greedily pick orbit covariants independent of symmetric span
basis = list(sym); chosen = []
for i, c in enumerate(cols):
    if sp.Matrix(basis + [c]).T.rank() > len(basis):
        basis.append(c); chosen.append(i)
print('new covariants from orbits', chosen)
# equivariance check at a random point for the chosen covariants
x = rand_tz()
for i in chosen:
    for g in rnd.sample(G, 5):
        gx = [None] * 9
        for j in range(9): gx[g[j]] = x[j]      # (g.x)_{g(j)} = x_j
        lhs = covariant(orbs[i], gx); rhs = [None] * 9; c = covariant(orbs[i], x)
        for j in range(9): rhs[g[j]] = c[j]
        assert lhs == rhs
print('equivariance verified')
with open('cov4.txt', 'w') as f:
    for i in chosen: f.write(repr(orbs[i][0]) + '  orbit size %d\n' % len(orbs[i]))
for i in chosen: print('orbit rep', orbs[i][0], ' size', len(orbs[i]))
