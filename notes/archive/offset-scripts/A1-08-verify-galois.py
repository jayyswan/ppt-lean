import sympy as sp
import mpmath as mp
from sympy import Rational as R

mp.mp.dps = 60
t = sp.symbols('t')

def chebotarev(Pexpr, t, primes):
    from collections import Counter
    types = Counter()
    for q in primes:
        try:
            fl = sp.factor_list(Pexpr, modulus=q)[1]
            sig = tuple(sorted([sp.Poly(f, t, modulus=q).degree() for f, m in fl for _ in range(m)]))
            types[tuple(sorted(sp.Poly(f,t,modulus=q).degree() for f,m in fl for _ in range(m)))] += 1
        except Exception:
            pass
    return types

def study(p, dval, label):
    p = sp.expand(p); pp = sp.diff(p, t)
    P = sp.expand(p**2*(1+pp**2) - dval**2)
    Pp = sp.Poly(P, t); N = Pp.degree()
    print("="*70)
    print(label, " N =", N, " irreducible:", Pp.is_irreducible)
    # X = t + p p'
    R = sp.factor(sp.resultant(P, sp.Symbol('X') - (t + p*pp), t))
    Rx = sp.Poly(R, sp.Symbol('X'))
    print(" X-minpoly deg:", Rx.degree(), " irreducible:", Rx.is_irreducible)
    # real roots of P and genuine check
    for r in sp.real_roots(Pp):
        t0 = sp.N(r, 50)
        pv = sp.N(p.subs(t,t0), 50); ppv = sp.N(pp.subs(t,t0), 50)
        w = sp.sqrt(1+ppv**2); lhs = sp.N(pv*w, 50)
        X0 = sp.N(t0 + pv*ppv, 50)
        print("   t0 = %s   p*w = %s   X0 = %s" % (sp.N(t0,40), sp.N(lhs,40), sp.N(X0,40)))
        # verify X0 satisfies Rx
        val = sp.N(Rx.as_expr().subs(sp.Symbol('X'), X0), 40)
        print("      Rx(X0) ~", sp.N(val, 8))
    # chebotarev
    primes = [29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109]
    ct = chebotarev(Pp.as_expr(), t, primes)
    print(" factor types mod primes (count):", dict(ct))

study(t**4 + t + 1, -1, "quartic p=t^4+t+1, d=-1")
