import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')
A, B, C, d = sp.symbols('A B C d')
cc = sp.symbols('c0:4'); ee = sp.symbols('e0:4')
x = sum(cc[i]*t**i for i in range(4)); y = sum(ee[i]*t**i for i in range(4))
F = sp.expand((A*x+B*y-C)**2*(sp.diff(x,t)**2+sp.diff(y,t)**2) - d**2*(B*sp.diff(x,t)-A*sp.diff(y,t))**2)
params = list(cc)+list(ee)+[A,B,C,d]
base = [R(1,3)+R(i,7) for i in range(len(params))]

def raw(vals):
    Fe = sp.expand(F.subs(dict(zip(params,vals))))
    P = sp.Poly(Fe,t)
    return P.degree(), P.all_coeffs()

print("base degree, LC:", raw(base)[0], raw(base)[1][0])
h = R(1,50)
rows=[]
for i in range(len(params)):
    vp=list(base); vp[i]+=h
    vm=list(base); vm[i]-=h
    dp,cp=raw(vp); dm,cm=raw(vm)
    if dp!=10 or dm!=10:
        print("param",i,"deg drop",dp,dm)
    rows.append([sp.nsimplify((cp[k]-cm[k])/(2*h)) for k in range(11)])
Jraw = sp.Matrix(rows).T
print("raw coeff rank (11 x 12):", Jraw.rank())

# monic normalized
def monic(vals):
    P=sp.Poly(sp.expand(F.subs(dict(zip(params,vals)))),t)
    c=P.all_coeffs(); return [sp.nsimplify(ci/c[0]) for ci in c]
rows2=[]
for i in range(len(params)):
    vp=list(base); vp[i]+=h
    vm=list(base); vm[i]-=h
    cp=monic(vp); cm=monic(vm)
    rows2.append([sp.nsimplify((cp[k]-cm[k])/(2*h)) for k in range(11)])
Jm=sp.Matrix(rows2).T
print("monic rank (11 x 12):", Jm.rank(), "codim in 10:", 10-Jm.rank())
