"""Session 12: can square roots of PSL(2,8)-invariant sextics remove the V4 obstruction for lines?

V4 = translations of F_8 by W = {0,1,2,3}. V4-fixed points of the weighted model of a square-root
tower lie (i) over the eigenlines [e] in P(V_chi), chi nontrivial (V_chi = span(e1_chi, e2_chi),
e1 = chi on W, e2 = chi on W+4), and (ii) over Pi = V^{V4}.
(i) Radicand f of degree d swaps at [e] iff f(e) != 0 and chi(h)^(d/2) = -1 for some h, i.e. d = 2 mod 4.
    p2(s e1 + t e2) = 4(s^2 + t^2) vanishes at t = +-i s; check the degree-6 invariants there.
(ii) For radicands vanishing on Pi to order 2, the swap needs the normal Hessians restricted to
    each V_chi (binary quadratics in (s, t)) to have no common zero.
"""
import random, itertools
import sympy as sp
from psl28 import G, invariant_orbits, eval_mon

W = [0, 1, 2, 3]
def chi_val(alpha, v):  # v in W as bits, alpha in {1,2,3}
    return (-1) ** bin(alpha & v).count('1')
s, t, a, b, eps = sp.symbols('s t a b eps')

orbs6 = invariant_orbits(6)
def inv(orb, x): return sp.expand(sum(eval_mon(m, x) for m in orb))

# basis of degree-6 invariants on V: evaluate on generic trace-zero symbolic point? Use restriction
# to the 8-dim V via x8 = -sum. Rank via random rational points.
rnd = random.Random(7)
def rand_V():
    x = [sp.Rational(rnd.randint(-50, 50)) for _ in range(8)]
    return x + [-sum(x)]
pts = [rand_V() for _ in range(len(orbs6) + 6)]
M = sp.Matrix([[sum(eval_mon(m, x) for m in o) for o in orbs6] for x in pts])
# columns basis of the 7-dim space of invariants on V
_, piv = M.rref()
basis = [orbs6[i] for i in piv]
print("degree-6 invariants on V:", len(basis))

def Pi_pt(a_, b_):
    x = [0] * 9
    for i in W: x[i] = a_
    for i in W: x[4 + i] = b_
    x[8] = -4 * (a_ + b_)
    return x

# (ii) subspace vanishing on Pi
rows = []
for o in basis:
    rows.append(sp.Poly(inv(o, Pi_pt(a, b)), a, b))
monos = sorted({m for r in rows for m in r.monoms()})
A = sp.Matrix([[r.coeff_monomial(a**m[0] * b**m[1]) for r in rows] for m in monos])
ker = A.nullspace()
print("vanishing on Pi:", len(ker))
def comb(vec, x): return sp.expand(sum(c * inv(o, x) for c, o in zip(vec, basis)))

# (i) values at isotropic V4-eigenvectors, all 7 basis invariants
print("\n(i) values at isotropic eigenvectors e = e1 + i e2 (s = 1):")
for alpha in (1, 2, 3):
    for sign in (1, -1):
        e = [0] * 9
        for v in W:
            e[v] = chi_val(alpha, v)
            e[4 + v] = sign * sp.I * chi_val(alpha, v)
        vals = [sp.simplify(inv(o, e)) for o in basis]
        print(f"  chi={alpha} t={'+' if sign > 0 else '-'}i:", vals)

# (ii) normal Hessians on V_chi for the Pi-vanishing combinations
print("\n(ii) normal Hessians on V_chi at a general point of Pi:")
for k, vec in enumerate(ker):
    for alpha in (1, 2, 3):
        n = [0] * 9
        for v in W:
            n[v] = s * chi_val(alpha, v)
            n[4 + v] = t * chi_val(alpha, v)
        x = [Pi_pt(a, b)[i] + eps * n[i] for i in range(9)]
        f = sp.Poly(comb(vec, x), eps)
        c1 = sp.expand(f.coeff_monomial(eps))
        c2 = sp.factor(f.coeff_monomial(eps**2))
        print(f"  f{k} chi={alpha}: eps^1 coeff {c1}, eps^2 coeff {c2}")

# common zeros of the normal Hessians on P(V_chi), as (a:b) varies
print("\nresultants in (s:t) of the Hessian quadratics (factored, in a, b):")
hess = {}
for k, vec in enumerate(ker):
    for alpha in (1, 2, 3):
        n = [0] * 9
        for v in W:
            n[v] = s * chi_val(alpha, v); n[4 + v] = t * chi_val(alpha, v)
        x = [Pi_pt(a, b)[i] + eps * n[i] for i in range(9)]
        q = sp.Poly(comb(vec, x), eps).coeff_monomial(eps**2)
        hess[(k, alpha)] = sp.factor(q / (a - b)).subs(t, 1)
for alpha in (1, 2, 3):
    r01 = sp.factor(sp.resultant(hess[(0, alpha)], hess[(1, alpha)], s))
    r02 = sp.factor(sp.resultant(hess[(0, alpha)], hess[(2, alpha)], s))
    r12 = sp.factor(sp.resultant(hess[(1, alpha)], hess[(2, alpha)], s))
    g = sp.factor(sp.gcd(sp.gcd(sp.numer(sp.together(r01)), sp.numer(sp.together(r02))), sp.numer(sp.together(r12))))
    print(f" chi={alpha}: gcd of pairwise resultants = {g}")
    print("   r01 =", r01)
