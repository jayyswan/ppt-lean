import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')
A, B, C, d = sp.symbols('A B C d')

def ranks_auto(F, params):
    base = {p: R(1,3)+R(i,7) for i,p in enumerate(params)}
    def P(expr): return sp.Poly(sp.expand(expr.subs(base)), t)
    P0 = P(F); N = P0.degree(); c0 = P0.all_coeffs(); lc = c0[0]
    mon = [sp.nsimplify(ci/lc) for ci in c0[1:]]
    cols=[]; cols2=[]
    for p in params:
        cj = P(sp.diff(F,p)).all_coeffs()
        if len(cj) < N+1: cj = [0]*(N+1-len(cj))+cj
        cols.append(cj); d_lc = cj[0]
        cols2.append([sp.nsimplify((cj[i+1]-mon[i]*d_lc)/lc) for i in range(N)])
    return N, sp.Matrix(cols).T.rank(), sp.Matrix(cols2).T.rank()

def num(Fr): return sp.numer(sp.together(sp.expand(Fr)))

aa,bb=sp.symbols('aa bb')
# ellipse / hyperbola genuine crossing: use G + dH/w form cleared minimally:
# w = sqrt(Qn)/Qd ; use unsquared polynomial identity F = G^2 Q - d^2 H^2 with G,H,Q in lowest terms
def conic_F(x,y):
    xp=sp.diff(x,t); yp=sp.diff(y,t)
    G=sp.together(A*x+B*y-C); Gn,Gd=sp.fraction(G)
    H=sp.together(B*xp-A*yp); Hn,Hd=sp.fraction(H)
    Q=sp.together(xp**2+yp**2); Qn,Qd=sp.fraction(Q)
    # F = Gn^2 Qn Hd^2 - d^2 Hn^2 Gd^2 Qd  (clears denominators, minimal-ish)
    return sp.expand(Gn**2*Qn*Hd**2 - d**2*Hn**2*Gd**2*Qd)

for (p_,q_) in [(-1,1),(-2,1)]:
    a1=sp.symbols('a1'); x=t**q_; y=a1*t**p_
    F=num((A*x+B*y-C)**2*(sp.diff(x,t)**2+sp.diff(y,t)**2)-d**2*(B*sp.diff(x,t)-A*sp.diff(y,t))**2)
    try:
        N,rr,mr=ranks_auto(F,[a1,A,B,C,d])
        print("power x^(%d/%d): N=%d raw=%d mon=%d codim=%d"%(p_,q_,N,rr,mr,N-mr))
    except Exception as ex:
        print("power x^(%d/%d) ERR %s"%(p_,q_,str(ex)[:50]))

xel=aa*(1-t**2)/(1+t**2); yel=2*bb*t/(1+t**2)
Fel=conic_F(xel,yel)
for nm,F,ps in [('ellipse',Fel,[aa,bb,A,B,C,d])]:
    try:
        N,rr,mr=ranks_auto(F,ps)
        print("%s: N=%d raw=%d mon=%d"%(nm,N,rr,mr))
    except Exception as ex:
        print(nm,"ERR",str(ex)[:60])
