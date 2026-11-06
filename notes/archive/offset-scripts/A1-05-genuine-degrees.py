import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')
A, B, C, d = R(2), R(3), R(7), R(1)

def genuine_deg(x, y, subs):
    x = sp.together(x.subs(subs)); y = sp.together(y.subs(subs))
    xp = sp.together(sp.diff(x, t)); yp = sp.together(sp.diff(y, t))
    Q = sp.together(xp**2 + yp**2)
    Qn, Qd = sp.fraction(Q)
    Qn = sp.expand(Qn); Qd = sp.expand(Qd)
    G = sp.together(A*x + B*y - C); Gn, Gd = sp.fraction(G)
    H = sp.together(B*xp - A*yp); Hn, Hd = sp.fraction(H)
    Ntot = sp.expand(Qn*Qd)
    fac = sp.factor(Ntot)
    fl = sp.factor_list(fac)[1]
    perfect = all(e % 2 == 0 for _, e in fl)
    if perfect:
        sq = sp.expand(sp.prod([b**(e//2) for b, e in fl]))
        E = sp.expand(Gn*Hd*sq + d*Hn*Gd*Qd)
        return sp.Poly(E, t).degree(), 'PH(ratio)', sp.Poly(E, t)
    term1 = sp.expand((Gn*Hd)**2 * Ntot)
    term2 = sp.expand(d**2 * (Hn*Gd*Qd)**2)
    F = sp.expand(term1 - term2)
    g = sp.gcd(sp.Poly(term1, t), sp.Poly(term2, t))
    return sp.Poly(F, t).degree() - g.degree(), 'irr(gcd=%d)' % g.degree(), sp.Poly(F, t)

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

print("%-30s %-6s %-14s %s" % ("family", "crossDeg", "type", "Fdeg"))
for name, (x, y, subs) in fams.items():
    try:
        dg, typ, Fp = genuine_deg(x, y, subs)
    except Exception as ex:
        dg, typ, Fp = 'err', str(ex)[:30], None
    print("%-30s %-6s %-14s %s" % (name, dg, typ, sp.Poly(Fp, t).degree() if Fp is not None else ''))
