import sympy as sp
from sympy import Rational as R

t, X, Y = sp.symbols('t X Y')

def offset_implicit(x, y, dval, subs):
    x = sp.together(x.subs(subs)); y = sp.together(y.subs(subs))
    xp = sp.together(sp.diff(x, t)); yp = sp.together(sp.diff(y, t))
    E1 = sp.together((X-x)**2 + (Y-y)**2 - dval**2)
    E2 = sp.together((X-x)*xp + (Y-y)*yp)
    E1n, E1d = sp.fraction(E1); E2n, E2d = sp.fraction(E2)
    # clear denominators
    E1p = sp.expand(E1n*E2d**2)
    E2p = sp.expand(E2n*E1d*E2d)
    Rres = sp.factor(sp.resultant(E1p, E2p, t))
    fl = sp.factor_list(Rres)[1]
    degs = []
    for f, m in fl:
        pf = sp.Poly(f, X, Y)
        if pf.total_degree() > 0:
            degs.append((pf.total_degree(), m, str(f)[:60]))
    return sp.Poly(Rres, X, Y).total_degree(), degs

def genus_of(x, y, subs):
    x = sp.together(x.subs(subs)); y = sp.together(y.subs(subs))
    xp = sp.together(sp.diff(x, t)); yp = sp.together(sp.diff(y, t))
    Q = sp.together(xp**2 + yp**2)
    Qn, Qd = sp.fraction(Q)
    Ntot = sp.expand(Qn*Qd)
    fl = sp.factor_list(Ntot)[1]
    sf = sp.prod([b**(e % 2) for b, e in fl])
    sf = sp.expand(sf)
    d = sp.Poly(sf, t).degree()
    return (d-1)//2, d

fams = {}
for n in range(1, 7):
    a = sp.symbols('a0:%d' % (n+1))
    p = sum(a[i]*t**i for i in range(n+1))
    fams['poly_graph deg%d' % n] = (t, p, {a[i]: R(2*i+1, i+2) for i in range(n+1)})
aa, bb = sp.symbols('aa bb', positive=True)
fams['ellipse'] = (aa*(1-t**2)/(1+t**2), 2*bb*t/(1+t**2), {aa: R(3), bb: R(2)})
fams['hyperbola'] = (aa*(1+t**2)/(1-t**2), 2*bb*t/(1-t**2), {aa: R(3), bb: R(2)})
cc = sp.symbols('c0:4'); ee = sp.symbols('e0:4')
fams['cubic pair general'] = (sum(cc[i]*t**i for i in range(4)), sum(ee[i]*t**i for i in range(4)),
                              {cc[i]: R(2*i+1, 5) for i in range(4)} | {ee[i]: R(3*i+2, 7) for i in range(4)})
fams['cuspidal (t^2,t^3)'] = (t**2, t**3, {})
lam = sp.symbols('lam')
fams['nodal (t^2+l,t^3+lt)'] = (t**2+lam, t**3+lam*t, {lam: R(2,3)})
fams['PH cubic (t-t^3/3,t^2)'] = (t - t**3/3, t**2, {})
fams['line (t,0)'] = (t, 0, {})
for (p_, q_) in [(3,2),(1,3),(2,3),(3,1),(-1,1),(-2,1)]:
    a1 = sp.symbols('a1')
    fams['power x^(%d/%d)' % (p_, q_)] = (t**q_, a1*t**p_, {a1: R(3,2)})

print("%-30s %-6s %-6s  %s" % ("family", "implicitDeg", "genus", "factors (deg,mult)"))
for name, (x, y, subs) in fams.items():
    try:
        tot, degs = offset_implicit(x, y, R(1), subs)
    except Exception as ex:
        tot, degs = 'err', str(ex)[:40]
    try:
        g, sfd = genus_of(x, y, subs)
    except Exception as ex:
        g, sfd = 'err', str(ex)[:20]
    print("%-30s %-6s %-6s  %s" % (name, tot, g, degs))
