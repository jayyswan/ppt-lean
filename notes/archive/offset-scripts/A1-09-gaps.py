import sympy as sp
from sympy import Rational as R

t, X, Y = sp.symbols('t X Y')
Xv = sp.Symbol('X')

# ---------- 1. offset implicit degree for rational curves, correct clearing ----------
def offset_implicit(x, y, dval, subs):
    x = sp.together(x.subs(subs)); y = sp.together(y.subs(subs))
    D = sp.lcm(sp.denom(x), sp.denom(y))
    xn = sp.expand(x*D); yn = sp.expand(y*D)
    Dp = sp.diff(D, t)
    xpn = sp.expand(sp.diff(xn,t)*D - xn*Dp)
    ypn = sp.expand(sp.diff(yn,t)*D - yn*Dp)
    E1 = sp.expand((X*D-xn)**2 + (Y*D-yn)**2 - dval**2*D**2)
    E2 = sp.expand((X*D-xn)*xpn + (Y*D-yn)*ypn)
    Rres = sp.factor(sp.resultant(E1, E2, t))
    fl = sp.factor_list(Rres)[1]
    out = []
    for f,m in fl:
        pf = sp.Poly(f, X, Y)
        if pf.total_degree() > 0:
            out.append((pf.total_degree(), m, str(sp.Poly(f,X,Y).as_expr())[:50]))
    return sp.Poly(Rres,X,Y).total_degree(), out

aa,bb=sp.symbols('aa bb', positive=True)
xel=aa*(1-t**2)/(1+t**2); yel=2*bb*t/(1+t**2)
xhy=aa*(1+t**2)/(1-t**2); yhy=2*bb*t/(1-t**2)
for nm,(x,y) in [('ellipse',(xel,yel)),('hyperbola',(xhy,yhy))]:
    tot,out = offset_implicit(x,y,R(1),{aa:R(3),bb:R(2)})
    print(nm, "res deg", tot, "factors:", out)

# ---------- 2. recovery degree for power laws ----------
def rec_deg(x,y,subs):
    x=x.subs(subs); y=y.subs(subs)
    F=sp.together((Xv-x)*sp.diff(x,t)+(Y-y)*sp.diff(y,t))
    n,d=sp.fraction(F)
    return sp.Poly(sp.expand(n),t).degree()
a1=sp.symbols('a1')
for (p_,q_) in [(3,2),(1,3),(2,3),(3,1),(-1,1),(-2,1)]:
    dg=rec_deg(t**q_, a1*t**p_, {a1:R(3,2)})
    print("power x^(%d/%d) recovery deg (raw fraction):"%(p_,q_), dg)

# 2b recovery deg for graphs
for n in range(2,7):
    a=sp.symbols('a0:%d'%(n+1)); p=sum(a[i]*t**i for i in range(n+1))
    F=sp.together((Xv-t) + (Y-p)*sp.diff(p,t))
    print("graph deg%d recovery deg:"%n, sp.Poly(sp.numer(F),t).degree())

# ---------- 3. cusp polynomial degree: d^2 N^2 - Q^3, N=x'y''-y'x'', Q=x'^2+y'^2 ----------
def cusp_deg(x,y,subs={}):
    x=x.subs(subs); y=y.subs(subs)
    xp=sp.diff(x,t); yp=sp.diff(y,t)
    N=xp*sp.diff(y,t,2)-yp*sp.diff(x,t,2)
    Q=xp**2+yp**2
    F=sp.together(sp.numer(N)**2 - Q**3)
    return sp.Poly(sp.expand(F),t).degree()
for n in range(2,7):
    a=sp.symbols('a0:%d'%(n+1)); p=sum(a[i]*t**i for i in range(n+1))
    sub={a[i]:R(2*i+1,i+2) for i in range(n+1)}
    print("graph deg%d cusp poly deg:"%n, cusp_deg(t,p,sub))
print("ellipse cusp poly deg:", cusp_deg(xel,yel,{aa:R(3),bb:R(2)}))
print("hyperbola cusp poly deg:", cusp_deg(xhy,yhy,{aa:R(3),bb:R(2)}))
cc=sp.symbols('c0:4'); ee=sp.symbols('e0:4')
xcp=sum(cc[i]*t**i for i in range(4)); ycp=sum(ee[i]*t**i for i in range(4))
print("cubic pair cusp poly deg:", cusp_deg(xcp,ycp,{cc[i]:R(2*i+1,5) for i in range(4)}|{ee[i]:R(3*i+2,7) for i in range(4)}))
