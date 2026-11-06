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
    P = sp.Poly(sp.expand(F.subs(dict(zip(params,vals)))),t)
    return P.all_coeffs()

for hden in [50, 10**3, 10**5, 10**7]:
    h = R(1,hden)
    rows=[]
    for i in range(len(params)):
        vp=list(base); vp[i]+=h
        vm=list(base); vm[i]-=h
        cp=raw(vp); cm=raw(vm)
        rows.append([sp.nsimplify((cp[k]-cm[k])/(2*h)) for k in range(11)])
    r=sp.Matrix(rows).T.rank()
    print("h=1/%d  raw rank = %d" % (hden, r))
