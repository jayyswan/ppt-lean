import sympy as sp
from sympy import Rational as R

t, X, Y, d = sp.symbols('t X Y d')

def crossed_poly(x, y, t, params):
    xp = sp.diff(x, t); yp = sp.diff(y, t)
    A, B, C = sp.symbols('A B C')
    G = A*x + B*y - C
    Q = sp.together(xp**2 + yp**2)
    H = sp.together(B*xp - A*yp)
    F = sp.together(G**2 * Q - d**2 * H**2)
    num, den = sp.fraction(F)
    num = sp.expand(num)
    return sp.Poly(num, t), (num, den)

def rec_poly(x, y, t):
    xp = sp.diff(x, t); yp = sp.diff(y, t)
    F = sp.together((X - x)*xp + (Y - y)*yp)
    num, den = sp.fraction(F)
    return sp.Poly(sp.expand(num), t)

def crossed_degree(x, y, t):
    P, _ = crossed_poly(x, y, t, None)
    return P.degree()

def rec_degree(x, y, t):
    return rec_poly(x, y, t).degree()

print("== crossing & recovery degrees ==")
fams = {}
# graphs
for n in range(1,7):
    a = sp.symbols('a0:%d' % (n+1))
    p = sum(a[i]*t**i for i in range(n+1))
    fams['poly_graph deg%d' % n] = (t, p)
# parabola scaled, hyperbola, ellipse rational
a,b = sp.symbols('a b', positive=True)
fams['ellipse'] = (a*(1-t**2)/(1+t**2), 2*b*t/(1+t**2))
fams['hyperbola'] = (a*(1+t**2)/(1-t**2), 2*b*t/(1-t**2))
# general cubic pair
c = sp.symbols('c0:4'); e = sp.symbols('e0:4')
fams['cubic pair (general)'] = (sum(c[i]*t**i for i in range(4)), sum(e[i]*t**i for i in range(4)))
# special cubics
fams['cuspidal (t^2,t^3)'] = (t**2, t**3)
lam = sp.symbols('lam')
fams['nodal/acnodal (t^2+l,t^3+lt)'] = (t**2+lam, t**3+lam*t)
fams['PH cubic (t-t^3/3,t^2)'] = (t - t**3/3, t**2)
# power laws
for (p_,q_) in [(3,2),(1,3),(2,3),(3,1),(-1,1),(-2,1)]:
    aa = sp.symbols('aa')
    if p_>0:
        fams['power x^(%d/%d)'%(p_,q_)] = (t**q_, aa*t**p_)
    else:
        fams['power x^(%d/%d)'%(p_,q_)] = (t**q_, aa*t**p_)

for name,(x,y) in fams.items():
    try:
        cd = crossed_degree(x,y,t)
        rd = rec_degree(x,y,t)
    except Exception as ex:
        cd = 'err'; rd = str(ex)[:30]
    print("%-32s crossingdeg=%-4s recoverydeg=%s" % (name, cd, rd))
