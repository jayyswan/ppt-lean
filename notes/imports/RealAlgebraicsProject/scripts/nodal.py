# Nodal fibre of S_ord (irreducible nodal odd cubic, node at a 2-torsion point).
# rho-coordinate on the normalization: line z_i(s) = rho_i (1 + s rho_i^2)/(1 - rho_i^2).
# Claim: rho_i are roots of A = Odd + g*Even where (X-1)^6 N(X) = Odd + Even (odd/even parts),
# N monic cubic chosen so that the even part has degree <= 2.  g is a free parameter.
import sympy as sp, numpy as np, mpmath as mp
X=sp.symbols('X'); n0,n1,n2=sp.symbols('n0 n1 n2')
G=sp.expand((X-1)**6*(X**3+n2*X**2+n1*X+n0))
eqs=[G.coeff(X,k) for k in (8,6,4)]
sols=sp.solve(eqs,[n0,n1,n2],dict=True)
print('solutions for N:',sols)
for so in sols:
    Gs=sp.expand(G.subs(so))
    Odd=sum(Gs.coeff(X,k)*X**k for k in range(1,10,2)); Ev=sp.expand(Gs-Odd)
    print('Odd =',Odd,'\nEven=',Ev)
    mp.mp.dps=40
    for g in [sp.Rational(1,3), sp.Rational(-2,7), 5]:
        A=sp.Poly(sp.expand(Odd+g*Ev),X)
        rts=[complex(r) for r in sp.Poly(A).nroots(n=40)]
        rts=[mp.mpc(r) for r in sp.Poly(A).nroots(n=40)]
        s=mp.mpf('0.41')
        z=[r*(1+s*r**2)/(1-r**2) for r in rts]
        nz=max(abs(t) for t in z)
        print(' g=',g,' nreal=',sum(1 for r in rts if abs(mp.im(r))<1e-20),
              ' p1,p3,p5,p7:',[mp.nstr(abs(sum(t**m for t in z))/nz**m,3) for m in (1,3,5,7)])
