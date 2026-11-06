import sympy as sp
from sympy import Rational as R

t, X, Y = sp.symbols('t X Y')
A, B, C, d = sp.symbols('A B C d')

def jac_rank(F, params, base, N):
    m = len(params)
    if base is None:
        base = [R(1, 3) + R(i, 7) for i in range(m)]
    def coeffs(vals):
        subs = dict(zip(params, vals))
        Fe = sp.expand(F.subs(subs))
        P = sp.Poly(Fe, t)
        c = P.all_coeffs()
        lc = c[0]
        return [sp.nsimplify(ci/lc) for ci in c[1:]]   # drop leading (monic)
    h = R(1, 50)
    rows = []
    for i in range(m):
        vp = list(base); vp[i] += h
        vm = list(base); vm[i] -= h
        cp = coeffs(vp); cm = coeffs(vm)
        rows.append([sp.nsimplify((cp[k]-cm[k])/(2*h)) for k in range(N)])
    J = sp.Matrix(rows).T   # N x m
    return J.rank(), m

def graph_F(n):
    a = sp.symbols('a0:%d' % (n+1))
    p = sum(a[i]*t**i for i in range(n+1))
    pp = sp.diff(p, t)
    F = (A*t + B*p - C)**2*(1+pp**2) - d**2*(B - A*pp)**2
    return F, list(a) + [A, B, C, d], 4*n-2

cc = sp.symbols('c0:4'); ee = sp.symbols('e0:4')
xcp = sum(cc[i]*t**i for i in range(4)); ycp = sum(ee[i]*t**i for i in range(4))
Fcp = (A*xcp + B*ycp - C)**2*(sp.diff(xcp,t)**2+sp.diff(ycp,t)**2) - d**2*(B*sp.diff(xcp,t)-A*sp.diff(ycp,t))**2

aa, bb = sp.symbols('aa bb')
xel = aa*(1-t**2)/(1+t**2); yel = 2*bb*t/(1+t**2)
Fel = sp.numer(sp.together((A*xel+B*yel-C)**2*(sp.diff(xel,t)**2+sp.diff(yel,t)**2) - d**2*(B*sp.diff(xel,t)-A*sp.diff(yel,t))**2))
xhy = aa*(1+t**2)/(1-t**2); yhy = 2*bb*t/(1-t**2)
Fhy = sp.numer(sp.together((A*xhy+B*yhy-C)**2*(sp.diff(xhy,t)**2+sp.diff(yhy,t)**2) - d**2*(B*sp.diff(xhy,t)-A*sp.diff(yhy,t))**2))
lam = sp.symbols('lam')
xno = t**2+lam; yno = t**3+lam*t
Fno = sp.numer(sp.together((A*xno+B*yno-C)**2*(sp.diff(xno,t)**2+sp.diff(yno,t)**2) - d**2*(B*sp.diff(xno,t)-A*sp.diff(yno,t))**2))
xcu = t**2; ycu = t**3
Fcu = sp.numer(sp.together((A*xcu+B*ycu-C)**2*(sp.diff(xcu,t)**2+sp.diff(ycu,t)**2) - d**2*(B*sp.diff(xcu,t)-A*sp.diff(ycu,t))**2))
xph = t - t**3/3; yph = t**2
Fph = sp.numer(sp.together((A*xph+B*yph-C)**2*(sp.diff(xph,t)**2+sp.diff(yph,t)**2) - d**2*(B*sp.diff(xph,t)-A*sp.diff(yph,t))**2))

tests = []
for n in range(2, 7):
    F, ps, N = graph_F(n)
    tests.append(('poly_graph deg%d' % n, F, ps, N))
tests.append(('cubic pair general', Fcp, list(cc)+list(ee)+[A,B,C,d], 10))
tests.append(('ellipse', Fel, [aa,bb,A,B,C,d], 8))
tests.append(('hyperbola', Fhy, [aa,bb,A,B,C,d], 8))
tests.append(('nodal cubic', Fno, [lam,A,B,C,d], 10))
tests.append(('cuspidal cubic', Fcu, [A,B,C,d], 8))
tests.append(('PH cubic', Fph, [A,B,C,d], 5))

print("%-24s %-4s %-4s %-6s %-6s" % ("family", "N", "rank", "codim", "m"))
for name, F, ps, N in tests:
    try:
        r, m = jac_rank(F, ps, None, N)
        print("%-24s %-4s %-4s %-6s %-6s" % (name, N, r, N-r, m))
    except Exception as ex:
        print("%-24s %-4s ERR %s" % (name, N, str(ex)[:40]))
