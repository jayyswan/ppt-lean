# Session 5, part 1: the composition family  m(t) = C(t)^3 + A(t)   (C monic cubic, A cubic).
# Claim: w = C(s) is a root of a fact 5 nonic, so real roots s of m lie in P.
import sympy as sp, random
from cypari import pari
t,w = sp.symbols('t w')
c2,c1,c0,a3,a2,a1,a0 = sp.symbols('c2 c1 c0 a3 a2 a1 a0')

def fact5_data(C, A):
    """return (xi, eta, lam) as polynomials in w with: eta^2 = xi (xi+lam)^2 on w = C(s), A(s) = -w^3"""
    a3_ = sp.Poly(A,t).coeff_monomial(t**3)
    q = sp.Poly(sp.expand(A - a3_*C), t)
    q2,q1,q0 = [q.coeff_monomial(t**k) for k in (2,1,0)]
    ts = -q1/(2*q2); qs = q0 - q1**2/(4*q2)
    Cs = sp.Poly(sp.expand(C.subs(t, t+ts)), t)          # C in t' = t - ts
    c2p,c1p,c0p = [Cs.coeff_monomial(t**k) for k in (2,1,0)]
    lam = c1p
    xi  = -(w**3 + a3_*w + qs)/q2
    eta = w - c2p*xi - c0p
    return xi, eta, lam, q2

# (1) symbolic identity for general C, A
C = t**3 + c2*t**2 + c1*t + c0; A = a3*t**3 + a2*t**2 + a1*t + a0
xi, eta, lam, q2 = fact5_data(C, A)
F = sp.together(eta**2 - xi*(xi+lam)**2)
N = sp.resultant(C - w, A + w**3, t)                     # = prod (C(s_j) - w) up to sign
ratio = sp.simplify(sp.together(F*q2**3) / N)
print('(1) q2^3 * (eta^2 - xi (xi+lam)^2) / Res_t(C - w, A + w^3) =', ratio)

# (2) target equations: power sums of the roots of C^3 + A with c2 = 0
m = sp.Poly(sp.expand((t**3 + c1*t + c0)**3 + A), t)
e = [(-1)**k * m.coeff_monomial(t**(9-k)) for k in range(10)]
p = [9]
for k in range(1,6):
    p.append(sp.expand(sum((-1)**(i-1)*e[i]*p[k-i] for i in range(1,k)) + (-1)**(k-1)*k*e[k]))
print('(2) p1 =', p[1], '| 6 p4 - p2^2 =', sp.expand(6*p[4]-p[2]**2), '| 18 p5 - 5 p2 p3 =', sp.expand(18*p[5]-5*p[2]*p[3]))

# (3) members with r = 1,3,5,7,9 real roots, irreducible, Galois group S_9, and the fact 5 nonic for w
random.seed(11)
found = {}
tries = 0
while len(found) < 5 and tries < 400000:
    tries += 1
    cc = [random.randint(-6,6) for _ in range(2)]; aa = [random.randint(-9,9) for _ in range(4)]
    Cn = t**3 + cc[0]*t + cc[1]; An = aa[0]*t**3 + aa[1]*t**2 + aa[2]*t + aa[3]
    if aa[1] == 0: continue                               # need q2 != 0 (here q2 = a2 since c2 = 0)
    mn = sp.Poly(sp.expand(Cn**3 + An), t)
    f = pari('Pol(%s)' % [int(x) for x in mn.all_coeffs()])
    r = int(pari.polsturm(f))
    if r in found: continue
    if not pari.polisirreducible(f): continue
    # S_9 test: Frobenius cycle types containing a 7-cycle type and a transposition type, plus irreducible => S_9
    has7 = has2 = False
    for pr in pari.primes(400):
        pr = int(pr)
        if int(pari.poldisc(f)) % pr == 0: continue
        degs = sorted(int(pari.poldegree(g_)) for g_ in pari.factormod(f, pr)[0])
        if degs == [1,1,7] or degs == [2,7]: has7 = True
        if degs.count(2) == 1 and all(d % 2 == 1 for d in degs if d != 2): has2 = True
    if not (has7 and has2): continue
    found[r] = (Cn, An, mn)
for r in sorted(found):
    Cn, An, mn = found[r]
    xi, eta, lam, q2n = fact5_data(Cn, An)
    # fact 5 nonic in w: U^3 + lam' U^2 + V^2 with U monic
    X = sp.expand(-xi - lam)              # Y^2 = -X^2 (X + lam), X = (w^3 + ...)/q2 - lam
    Fw = sp.Poly(sp.expand(q2n**3*(eta**2 + X**2*(X+lam))), w)
    Nw = sp.Poly(sp.resultant(Cn - w, An + w**3, t), w)
    assert sp.expand(Fw.as_expr()*Nw.LC() - Nw.as_expr()*Fw.LC()) == 0
    fw = pari('Pol(%s)' % [int(x) for x in (Nw*sp.sign(Nw.LC())).all_coeffs()])
    print('(3) r=%d: C = %s, A = %s | real roots of w-nonic: %d | q2 = %s, lambda = %s' % (r, Cn, An, int(pari.polsturm(fw)), q2n, lam))
