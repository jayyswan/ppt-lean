"""Exact check: the Klein group V4 < E < PSL(2,8) fixes no line on Q4.

V4 orbits on the 9 points: {1}, {2,3,4,6}, {5,7,8,9} (generators from abel.g).
Isotypic components of V (trace zero), each of dimension 2:
  V_0 = {(c, a,a,a,a, b,b,b,b) : c = -4(a+b)},  V_chi = {(0, a chi(h) on orbit 1, b chi(h) on orbit 2)}.
A V4-invariant 2-plane is a whole V_chi, or span(u, v) with u in V_chi, v in V_psi, chi != psi.
In the second case only the coefficients of x^4, x^2 y^2, y^4 in Q4(xu + yv) survive.
"""
import sympy as sp
from itertools import combinations

g1 = [1, 4, 6, 2, 7, 3, 5, 9, 8]
g2 = [1, 3, 2, 6, 9, 4, 8, 7, 5]
def act(g, i): return g[i - 1]
# group elements as (e1, e2) -> permutation
elts = {}
for e1 in range(2):
    for e2 in range(2):
        p = list(range(1, 10))
        for _ in range(e1): p = [act(g1, x) for x in p]
        for _ in range(e2): p = [act(g2, x) for x in p]
        elts[(e1, e2)] = p
o1, o2 = 2, 5  # base points of the two 4-orbits
a, b = sp.symbols('a b')
def vec(chi):
    x = [0] * 9
    if chi == (0, 0):
        x[0] = -4 * (a + b)
    for (e1, e2), p in elts.items():
        s = (-1) ** (chi[0] * e1 + chi[1] * e2)
        x[p[o1 - 1] - 1] = s * a
        x[p[o2 - 1] - 1] = s * b
    return x
chars = [(0, 0), (1, 0), (0, 1), (1, 1)]
def Q4(x):
    return sp.expand(6 * sum(t**4 for t in x) - sum(t**2 for t in x) ** 2)

# check these really are eigenvectors (each orbit point gets a single value)
for chi in chars:
    x = vec(chi)
    for g, e in [(g1, (1, 0)), (g2, (0, 1))]:
        gx = [0] * 9
        for i in range(9): gx[g[i] - 1] = x[i]
        s = (-1) ** (chi[0] * e[0] + chi[1] * e[1])
        assert all(sp.simplify(gx[i] - s * x[i]) == 0 for i in range(9)), chi

ok = True
for chi in chars:
    q = sp.factor(Q4(vec(chi)))
    print("Q4 on V_%s:" % (chi,), q)
    ok &= q != 0
t = sp.symbols('t')
a2, b2 = sp.symbols('a2 b2')
for c1, c2 in combinations(chars, 2):
    u = vec(c1)
    v = [sp.sympify(e).subs({a: a2, b: b2}, simultaneous=True) for e in vec(c2)]
    P = sp.Poly(Q4([ui + t * vi for ui, vi in zip(u, v)]), t)
    cs = [sp.expand(P.coeff_monomial(t**i)) for i in range(5)]
    assert cs[1] == 0 and cs[3] == 0
    # solve: cs[0](a,b) = 0, cs[4](a2,b2) = 0, cs[2] = 0, projectively in (a:b), (a2:b2)
    G = sp.groebner([cs[0].subs(b, 1), cs[4].subs(b2, 1), cs[2].subs({b: 1, b2: 1})], a, a2, order='lex')
    G2 = sp.groebner([cs[0].subs(a, 1), cs[4].subs(b2, 1), cs[2].subs({a: 1, b2: 1})], b, a2, order='lex')
    G3 = sp.groebner([cs[0].subs(b, 1), cs[4].subs(a2, 1), cs[2].subs({b: 1, a2: 1})], a, b2, order='lex')
    G4 = sp.groebner([cs[0].subs(a, 1), cs[4].subs(a2, 1), cs[2].subs({a: 1, a2: 1})], b, b2, order='lex')
    empty = all(list(g.exprs) == [1] for g in (G, G2, G3, G4))
    print(c1, c2, "no common solution" if empty else "SOLUTION EXISTS")
    ok &= empty
print("V4 fixes no line on Q4:", ok)
