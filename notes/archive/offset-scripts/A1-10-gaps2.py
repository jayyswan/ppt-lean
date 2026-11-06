import sympy as sp
from sympy import Rational as R

t, X, Y = sp.symbols('t X Y')
Xv = sp.Symbol('X')

def offset_implicit_D(x, y, D, dval, subs):
    x = sp.together(x.subs(subs)); y = sp.together(y.subs(subs))
    xn = sp.expand(x*D); yn = sp.expand(y*D)
    Dp = sp.diff(D, t)
    xpn = sp.expand(sp.diff(xn,t)*D - xn*Dp)
    ypn = sp.expand(sp.diff(yn,t)*D - yn*Dp)
    E1 = sp.expand((X*D-xn)**2 + (Y*D-yn)**2 - dval**2*D**2)
    E2 = sp.expand((X*D-xn)*xpn + (Y*D-yn)*ypn)
    Rres = sp.factor(sp.resultant(E1, E2, t))
    fl = sp.factor_list(Rres)[1]
    out = [(sp.Poly(f,X,Y).total_degree(), m) for f,m in fl if sp.Poly(f,X,Y).total_degree()>0]
    return sp.Poly(Rres,X,Y).total_degree(), out

aa,bb=sp.symbols('aa bb', positive=True)
xhy=aa*(1+t**2)/(1-t**2); yhy=2*bb*t/(1-t**2)
D = 1-t**2
try:
    tot,out = offset_implicit_D(xhy,yhy,D,R(1),{aa:R(3),bb:R(2)})
    print("hyperbola offset implicit res deg:", tot, "factors (deg,mult):", out)
except Exception as ex:
    print("hyperbola err", str(ex)[:80])

print()
a1=sp.symbols('a1')
for (p_,q_) in [(3,2),(1,3),(2,3),(3,1),(-1,1),(-2,1)]:
    x=t**q_; y=a1*t**p_
    F=sp.together((Xv-x)*sp.diff(x,t)+(Y-y)*sp.diff(y,t))
    n,dd=sp.fraction(F)
    print("power x^(%d/%d) recovery deg:"%(p_,q_), sp.Poly(sp.expand(sp.together(F).as_numer_denom()[0]),t).degree())
print()
for n in range(2,7):
    a=sp.symbols('a0:%d'%(n+1)); p=sum(a[i]*t**i for i in range(n+1))
    F=sp.together((Xv-t) + (Y-p)*sp.diff(p,t))
    print("graph deg%d recovery deg:"%n, sp.Poly(sp.numer(F),t).degree())
print()
def cusp_deg(x,y,subs={}):
    x=x.subs(subs); y=y.subs(subs)
    xp=sp.diff(x,t); yp=sp.diff(y,t)
    Nc=sp.together(xp*sp.diff(y,t,2)-yp*sp.diff(x,t,2))
    Q=sp.together(xp**2+yp**2)
    F=sp.together(sp.numer(Nc)**2 - Q**3)
    return sp.Poly(sp.expand(sp.numer(F)),t).degree()
for n in range(2,7):
    a=sp.symbols('a0:%d'%(n+1)); p=sum(a[i]*t**i for i in range(n+1))
    sub={a[i]:R(2*i+1,i+2) for i in range(n+1)}
    print("graph deg%d cusp poly deg:"%n, cusp_deg(t,p,sub))
print("ellipse cusp poly deg:", cusp_deg(aa*(1-t**2)/(1+t**2),2*bb*t/(1+t**2),{aa:R(3),bb:R(2)}))
cc=sp.symbols('c0:4'); ee=sp.symbols('e0:4')
xcp=sum(cc[i]*t**i for i in range(4)); ycp=sum(ee[i]*t**i for i in range(4))
print("cubic pair cusp poly deg:", cusp_deg(xcp,ycp,{cc[i]:R(2*i+1,5) for i in range(4)}|{ee[i]:R(3*i+2,7) for i in range(4)}))
