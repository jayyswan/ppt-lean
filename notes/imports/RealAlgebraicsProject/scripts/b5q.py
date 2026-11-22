# Session 63: exact identities for row B5.
# (1) I = B2^2/B3^3 = -(8/45) * gamma^2, gamma = skewness of the 10 values V_i = y_i^2.
# (2) Over Q: for u in a nonic field K and zeta = -Tr u, the 10-point conditions p3 = p5 = 0
#     read Tr(u^3) = (Tr u)^3, Tr(u^5) = (Tr u)^5; (w - zeta) chi_u(w) = E(w^2) + R(w).
import sympy as sp, random
from fractions import Fraction as Fr

p2, p4, p6 = sp.symbols('p2 p4 p6')
B3 = (p2**2 - 10*p4)/40
B2 = -(p2**3 - 15*p2*p4 + 50*p6)/300
m1, m2, m3 = p2/10, p4/10, p6/10           # moments of V_i = y_i^2 (10 values)
var = m2 - m1**2
mu3 = m3 - 3*m1*m2 + 2*m1**3
print('B3 + (5/2) var =', sp.simplify(B3 + sp.Rational(5, 2)*var))
print('B2 + (5/3) mu3 =', sp.simplify(B2 + sp.Rational(5, 3)*mu3))
I = B2**2/B3**3
print('I + (8/45) mu3^2/var^3 =', sp.simplify(I + sp.Rational(8, 45)*mu3**2/var**3))

# (2) random check over Q with exact rationals: build 9 numbers u_i (any), zeta = -sum,
# check the odd coefficients of prod (w - y) against p3, p5.
w = sp.symbols('w')
random.seed(1)
for trial in range(3):
    u = [Fr(random.randint(-20, 20), random.randint(1, 5)) for _ in range(9)]
    z = -sum(u)
    ys = u + [z]
    f = sp.expand(sp.prod([w - sp.Rational(y.numerator, y.denominator) for y in ys]))
    c = sp.Poly(f, w).all_coeffs()        # degree 10
    P = lambda k: sum(y**k for y in ys)
    # e1 = 0 always; e3 = p3/3 when e1 = 0; e5 relation via Newton
    print('trial', trial, 'w^9 coeff', c[1], ' p3 =', P(3), ' w^7 coeff =', c[3],
          ' check -p3/3 =', -Fr(P(3), 3) if True else None)
print('identities: Tr u^3 - (Tr u)^3 = p3^(10), Tr u^5 - (Tr u)^5 = p5^(10) (since zeta = -Tr u)')
