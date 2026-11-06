import sympy as sp
from sympy import Rational as R
t = sp.symbols('t')

def run(p):
    p = sp.expand(p); pp = sp.diff(p,t)
    P = sp.Poly(sp.expand(p**2*(1+pp**2)-1), t); N=P.degree()
    print("p=",p," N=",N," irred:",P.is_irreducible)
    for r in sp.real_roots(P):
        t0=sp.N(r,45)
        pv=sp.N(p.subs(t,t0),45); ppv=sp.N(pp.subs(t,t0),45)
        w=sp.sqrt(1+ppv**2); X0=t0+pv*ppv
        print("   t0=",sp.N(t0,40)," p*w=",sp.N(pv*w,40)," X0=",sp.N(X0,40))
    # chebotarev
    from collections import Counter
    c=Counter()
    for q in [37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127]:
        try:
            fl=sp.factor_list(P.as_expr(),modulus=q)[1]
            sig=tuple(sorted([sp.Poly(f,t,modulus=q).degree() for f,m in fl for _ in range(m)]))
            c[sig]+=1
        except Exception: pass
    print("   chebotarev types:",dict(c))

run(t**5+t+1)
run(t**6+t+1)
