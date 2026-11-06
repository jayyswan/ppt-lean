import sympy as sp

t, X = sp.symbols('t X')
p = t**4 + t + 1
pp = sp.diff(p, t)
d = 1
P = sp.expand(p**2*(1+pp**2) - d**2)
Pp = sp.Poly(P, t)
print("P degree", Pp.degree(), "LC", Pp.LC(), "irreducible:", Pp.is_irreducible)

f_num = sp.lambdify(t, P, 'mpmath')
import mpmath as mp
mp.mp.dps = 40

Q = sp.expand(X - t - p*pp)
print("Q degree in t:", sp.Poly(Q, t).degree())

for r in sp.real_roots(Pp):
    t0 = sp.N(r, 40)
    pv = sp.N(p.subs(t, t0), 40)
    ppv = sp.N(pp.subs(t, t0), 40)
    w = sp.sqrt(1 + ppv**2)
    lhs = sp.N(pv*w, 40)
    X0 = sp.N(t0 + pv*ppv, 40)
    print("t0 =", t0)
    print("   p(t0)=%s  p'(t0)=%s  p*w=%s  (|p*w| vs d=%d)" % (sp.N(pv,25), sp.N(ppv,25), lhs, d))
    Qn = sp.Poly(sp.expand(Q.subs(X, X0)), t)
    cr = sp.nroots(Qn, n=30)
    realr = [c for c in cr if abs(sp.im(c)) < sp.Float('1e-25')]
    complexr = [c for c in cr if abs(sp.im(c)) >= sp.Float('1e-25')]
    print("   Q roots: #real=%d #complex=%d  -> nonreal exists: %s" % (len(realr), len(complexr), len(complexr)>0))
    for c in complexr[:2]:
        print("      complex root ~", c)
    # minimal polynomial of X0
    print("   X0 ~", X0)
