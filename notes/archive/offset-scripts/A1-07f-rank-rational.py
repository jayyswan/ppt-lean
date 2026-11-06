import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')
A, B, C, d = sp.symbols('A B C d')

def ranks_auto(F, params):
    base = {p: R(1,3)+R(i,7) for i,p in enumerate(params)}
    def P(expr):
        return sp.Poly(sp.expand(expr.subs(base)), t)
    P0 = P(F)
    N = P0.degree()
    c0 = P0.all_coeffs()
    lc = c0[0]
    mon = [sp.nsimplify(ci/lc) for ci in c0[1:]]
    cols=[]; cols2=[]
    for p in params:
        cj = P(sp.diff(F,p)).all_coeffs()
        if len(cj) < N+1: cj = [0]*(N+1-len(cj))+cj
        cols.append(cj)
        d_lc = cj[0]
        cols2.append([sp.nsimplify((cj[i+1]-mon[i]*d_lc)/lc) for i in range(N)])
    return N, sp.Matrix(cols).T.rank(), sp.Matrix(cols2).T.rank()

def num(Fr): return sp.numer(sp.together(sp.expand(Fr)))

aa,bb=sp.symbols('aa bb')
xel=aa*(1-t**2)/(1+t**2); yel=2*bb*t/(1+t**2)
Fel = num((A*xel+B*yel-C)**2*(sp.diff(xel,t)**2+sp.diff(yel,t)**2)-d**2*(B*sp.diff(xel,t)-A*sp.diff(yel,t))**2)
xhy=aa*(1+t**2)/(1-t**2); yhy=2*bb*t/(1-t**2)
Fhy = num((A*xhy+B*yhy-C)**2*(sp.diff(xhy,t)**2+sp.diff(yhy,t)**2)-d**2*(B*sp.diff(xhy,t)-A*sp.diff(yhy,t))**2)
lam=sp.symbols('lam'); xno=t**2+lam; yno=t**3+lam*t
Fno=num((A*xno+B*yno-C)**2*(sp.diff(xno,t)**2+sp.diff(yno,t)**2)-d**2*(B*sp.diff(xno,t)-A*sp.diff(yno,t))**2)
xcu=t**2; ycu=t**3
Fcu=num((A*xcu+B*ycu-C)**2*(sp.diff(xcu,t)**2+sp.diff(ycu,t)**2)-d**2*(B*sp.diff(xcu,t)-A*sp.diff(ycu,t))**2)
xph=t-t**3/3; yph=t**2
Fph=num((A*xph+B*yph-C)**2*(sp.diff(xph,t)**2+sp.diff(yph,t)**2)-d**2*(B*sp.diff(xph,t)-A*sp.diff(yph,t))**2)

tests=[('ellipse',Fel,[aa,bb,A,B,C,d]),('hyperbola',Fhy,[aa,bb,A,B,C,d]),
       ('nodal cubic',Fno,[lam,A,B,C,d]),('cuspidal cubic',Fcu,[A,B,C,d]),
       ('PH cubic',Fph,[A,B,C,d])]
for (p_,q_) in [(3,2),(1,3),(2,3),(3,1)]:
    a1=sp.symbols('a1'); x=t**q_; y=a1*t**p_
    F=num((A*x+B*y-C)**2*(sp.diff(x,t)**2+sp.diff(y,t)**2)-d**2*(B*sp.diff(x,t)-A*sp.diff(y,t))**2)
    tests.append(('power x^(%d/%d)'%(p_,q_),F,[a1,A,B,C,d]))

print("%-22s %-4s %-8s %-8s %-6s" % ("family","N","rawrank","monrank","codim"))
for name,F,ps in tests:
    try:
        N,rr,mr=ranks_auto(F,ps)
        print("%-22s %-4s %-8s %-8s %-6s" % (name,N,rr,mr,N-mr))
    except Exception as ex:
        print("%-22s ERR %s" % (name,str(ex)[:50]))
