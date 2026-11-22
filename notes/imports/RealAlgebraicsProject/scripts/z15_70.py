# Z15 = W3 ∩ W5 in P^2(p,q,r) over Q, for k3 = k(kappa), kappa^3 = lam.
# Points (alpha, c) in k3 x k with 3Tr alpha^j + c^j = 0 (j=1,3,5), alpha = p+q kappa+r kappa^2, c = -9p.
import sys
from sympy import symbols, resultant, factor_list, Poly, expand, gcd, groebner
p,q,r = symbols('p q r')
lam = int(sys.argv[1]) if len(sys.argv)>1 else 10
W3 = lam*q**3 + lam**2*r**3 + 6*lam*p*q*r - 80*p**3
W5 = (p**5 + 10*lam*(p**2*q**3+2*p**3*q*r) + lam**2*(10*p**2*r**3+30*p*q**2*r**2+5*q**4*r) + 5*lam**3*q*r**4) - 6561*p**5
# points with r = 0
print("r=0:", factor_list(gcd(Poly(W3.subs(r,0),p,q), Poly(W5.subs(r,0),p,q)).as_expr()))
R = resultant(W3.subs(r,1), W5.subs(r,1), q)   # in p, degree <= 15
print("deg R =", Poly(R,p).degree())
fl = factor_list(R)
for f,e in fl[1]: print(Poly(f,p).degree(), e, f if Poly(f,p).degree()<=3 else '')
