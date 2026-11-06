import sympy as sp
from sympy import Rational as R

t = sp.symbols('t')

def ranks(F, params, N, base=None):
    """Exact Jacobian rank via coeffs of dF/dparam at a rational point."""
    if base is None:
        base = {p: R(1, 3) + R(i, 7) for i, p in enumerate(params)}
    dF = [sp.diff(F, p) for p in params]
    def coeffs_at(expr):
        P = sp.Poly(sp.expand(expr.subs(base)), t)
        return P.all_coeffs()   # descending, length deg+1
    # raw Jacobian: J[k][j] = coeff k of dF/dp_j ; all F have degree N => N+1 coeffs
    cols = []
    for j in range(len(params)):
        cj = coeffs_at(dF[j])
        if len(cj) != N+1:
            cj = [0]*(N+1-len(cj)) + cj
        cols.append(cj)
    Jraw = sp.Matrix(cols).T          # (N+1) x m
    c0 = coeffs_at(F)                  # includes LC
    lc = c0[0]
    mon = [sp.nsimplify(ci/lc) for ci in c0[1:]]   # N monic coeffs
    # monic Jacobian: dmi/dp_j = (deriv c_{i+1} - m_i deriv c_0)/lc
    cols2 = []
    for j in range(len(params)):
        cj = coeffs_at(dF[j])
        if len(cj) != N+1:
            cj = [0]*(N+1-len(cj)) + cj
        d_lc = cj[0]
        col = [sp.nsimplify((cj[i+1] - mon[i]*d_lc)/lc) for i in range(N)]
        cols2.append(col)
    Jmon = sp.Matrix(cols2).T         # N x m
    return Jraw.rank(), Jmon.rank()

# --- families ---
A, B, C, d = sp.symbols('A B C d')
tests = []
def graphF(n):
    a = sp.symbols('a0:%d' % (n+1))
    p = sum(a[i]*t**i for i in range(n+1)); pp = sp.diff(p,t)
    F = (A*t+B*p-C)**2*(1+pp**2) - d**2*(B-A*pp)**2
    return sp.expand(F), list(a)+[A,B,C,d], 4*n-2

for n in range(2,7):
    F,ps,N = graphF(n); tests.append(('poly_graph deg%d'%n,F,ps,N))

cc = sp.symbols('c0:4'); ee = sp.symbols('e0:4')
xcp=sum(cc[i]*t**i for i in range(4)); ycp=sum(ee[i]*t**i for i in range(4))
Fcp = sp.expand((A*xcp+B*ycp-C)**2*(sp.diff(xcp,t)**2+sp.diff(ycp,t)**2)
                - d**2*(B*sp.diff(xcp,t)-A*sp.diff(ycp,t))**2)
tests.append(('cubic pair general', Fcp, list(cc)+list(ee)+[A,B,C,d], 10))

aa,bb=sp.symbols('aa bb')
def num(Fr): return sp.numer(sp.together(sp.expand(Fr)))
xel=aa*(1-t**2)/(1+t**2); yel=2*bb*t/(1+t**2)
Fel = num((A*xel+B*yel-C)**2*(sp.diff(xel,t)**2+sp.diff(yel,t)**2)-d**2*(B*sp.diff(xel,t)-A*sp.diff(yel,t))**2)
tests.append(('ellipse', Fel, [aa,bb,A,B,C,d], 8))
xhy=aa*(1+t**2)/(1-t**2); yhy=2*bb*t/(1-t**2)
Fhy = num((A*xhy+B*yhy-C)**2*(sp.diff(xhy,t)**2+sp.diff(yhy,t)**2)-d**2*(B*sp.diff(xhy,t)-A*sp.diff(yhy,t))**2)
tests.append(('hyperbola', Fhy, [aa,bb,A,B,C,d], 8))
lam=sp.symbols('lam'); xno=t**2+lam; yno=t**3+lam*t
Fno=num((A*xno+B*yno-C)**2*(sp.diff(xno,t)**2+sp.diff(yno,t)**2)-d**2*(B*sp.diff(xno,t)-A*sp.diff(yno,t))**2)
tests.append(('nodal cubic', Fno, [lam,A,B,C,d], 10))
xcu=t**2; ycu=t**3
Fcu=num((A*xcu+B*ycu-C)**2*(sp.diff(xcu,t)**2+sp.diff(ycu,t)**2)-d**2*(B*sp.diff(xcu,t)-A*sp.diff(ycu,t))**2)
tests.append(('cuspidal cubic', Fcu, [A,B,C,d], 8))
xph=t-t**3/3; yph=t**2
Fph=num((A*xph+B*yph-C)**2*(sp.diff(xph,t)**2+sp.diff(yph,t)**2)-d**2*(B*sp.diff(xph,t)-A*sp.diff(yph,t))**2)
tests.append(('PH cubic', Fph, [A,B,C,d], 5))

print("%-24s %-4s %-6s %-6s %-6s" % ("family","N","rawrank","monrank","codim"))
for name,F,ps,N in tests:
    try:
        rr, mr = ranks(F, ps, N)
        print("%-24s %-4s %-6s %-6s %-6s" % (name,N,rr,mr,N-mr))
    except Exception as ex:
        print("%-24s %-4s ERR %s" % (name,N,str(ex)[:50]))
