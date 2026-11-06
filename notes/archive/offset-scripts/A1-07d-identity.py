import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')
A, B, C, d = sp.symbols('A B C d')
cc = sp.symbols('c0:4'); ee = sp.symbols('e0:4')
x = sum(cc[i]*t**i for i in range(4)); y = sum(ee[i]*t**i for i in range(4))
F = sp.expand((A*x+B*y-C)**2*(sp.diff(x,t)**2+sp.diff(y,t)**2) - d**2*(B*sp.diff(x,t)-A*sp.diff(y,t))**2)

# u = A x + B y - C ; v = B x - A y
u = A*x + B*y - C
v = B*x - A*y
up = sp.diff(u,t); vp = sp.diff(v,t)
NF = (u**2*(up**2+vp**2) - d**2*(A**2+B**2)*vp**2)/(A**2+B**2)
print("identity F == NF ?", sp.simplify(sp.expand(F - sp.together(NF))) == 0)

# rank of params -> (u coeffs(4), vp coeffs(3), T=A^2+B^2, d)
uP = sp.Poly(sp.expand(u), t); vpP = sp.Poly(sp.expand(vp), t)
print("deg u", uP.degree(), "deg vp", vpP.degree())
quants = uP.all_coeffs() + vpP.all_coeffs() + [A**2+B**2, d]
params = list(cc)+list(ee)+[A,B,C,d]
Jq = sp.Matrix(quants).jacobian(params)
base = {p: R(1,3)+R(i,7) for i,p in enumerate(params)}
Jnum = Jq.subs(base)
print("rank of map to (u,vp,T,d):", Jnum.rank(), "of", Jnum.shape)

# rank of map params -> F raw coeffs, symbolic Jacobian
FP = sp.Poly(F, t)
coeffs = FP.all_coeffs()
Jf = sp.Matrix(coeffs).jacobian(params)
print("computing symbolic Jacobian of 11 coeffs ...")
Jfn = Jf.subs(base)
print("rank of raw F coeff Jacobian:", Jfn.rank(), "of", Jfn.shape)
