# Cross-check: points of the sextic factor of Z15 (lam=10) map to conjugate triples proportional to roots of 3x^3-3x^2-15x+7
import numpy as np, cmath
from sympy import symbols, resultant, factor_list, Poly, nroots, solve
p,q = symbols('p q'); lam=10; r=1
W3 = lam*q**3 + lam**2*r**3 + 6*lam*p*q*r - 80*p**3
W5 = (p**5 + 10*lam*(p**2*q**3+2*p**3*q*r) + lam**2*(10*p**2*r**3+30*p*q**2*r**2+5*q**4*r) + 5*lam**3*q*r**4) - 6561*p**5
sext = [f for f,e in factor_list(resultant(W3,W5,q))[1] if Poly(f,p).degree()==6][0]
print("sextic:", sext)
g = np.roots([3,-3,-15,7]); g = g/g.sum()
k = 10**(1/3); w = cmath.exp(2j*cmath.pi/3)
for pv in nroots(sext, n=30):
    pv = complex(pv)
    qs = [complex(s) for s in nroots(Poly(W3.subs(p,pv),q))]
    qv = min(qs, key=lambda s: abs(complex(W5.subs({p:pv,q:s}))))
    xs = np.array([pv+qv*k*w**i+(k*w**i)**2 for i in range(3)]); xs = xs/xs.sum()
    print(round(abs(complex(W5.subs({p:pv,q:qv}))),8), sorted(np.round(xs.real,6)), round(max(abs(xs.imag)),6), sorted(np.round(g,6)))
