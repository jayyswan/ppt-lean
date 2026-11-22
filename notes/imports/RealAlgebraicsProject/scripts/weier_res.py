# Session 5, part 2: Weierstrass form of a nonic.
# m = t^9 + m7 t^7 + ... + m0 (trace zero).  Seek m = g(U) + V^2, U = t^3 + u t, g monic cubic, V cubic.
import sympy as sp
t,X = sp.symbols('t X')
u,m6,m5,m4,m3,m2,m1,m0 = sp.symbols('u m6 m5 m4 m3 m2 m1 m0')   # m7 = 3u
rho = sp.symbols('rho')            # rho = v3^2
A5 = m5 - 3*u**2; A4 = m4 - 2*u*m6; A2 = m2 - u**2*m6; A1 = m1 - u*(m3 - u**3)
# everything below is even in v3, so write products that are rational in rho
v2v3 = A5/2                                   # v2 v3
v2sq = A5**2/(4*rho)
v1v3 = (A4 + 2*u*rho - v2sq)/2                # v1 v3
v1v2 = v1v3*v2v3/rho
v1sq = v1v3**2/rho
v0v3 = sp.together((A1 + 2*u*v1v2)*4*rho**2/(4*A4*rho - A5**2))   # from E1
v0v2 = v0v3*v2v3/rho
E2 = sp.together(v1sq + 2*v0v2 - u**2*rho - A2)
num, den = sp.fraction(sp.together(E2))
R = sp.Poly(sp.expand(num), rho)
print('resolvent degree in rho:', R.degree(), '| denominator:', sp.factor(den))
R = sp.Poly(sp.factor(R.as_expr()), rho)
co = [sp.factor(c) for c in R.all_coeffs()]
print('leading coeff:', co[0]); print('constant coeff:', co[-1])
# u = 0 shape
print('u = 0:', sp.factor(R.as_expr().subs(u,0)))
g2 = m6 - rho
g1 = sp.together(m3 - u**3 - 2*v0v3 - 2*v1v2)
g0 = sp.together(m0 - v0v3**2/rho)
# identity check: with numeric values, reconstruct and compare
import random
random.seed(3)
vals = {u: sp.Rational(random.randint(-3,3)), m6:random.randint(-4,4), m5:random.randint(-4,4), m4:random.randint(-4,4),
        m3:random.randint(-4,4), m2:random.randint(-4,4), m1:random.randint(-4,4), m0:random.randint(-4,4)}
Rn = sp.Poly(R.as_expr().subs(vals), rho)
print('numeric resolvent:', Rn.as_expr(), '| irreducible:', Rn.is_irreducible)
ok = True
for rt in sp.Poly(Rn, rho).nroots(n=40):
    r_ = rt
    v3 = sp.sqrt(r_); 
    v2 = (A5/2).subs(vals)/v3; v1 = (v1v3.subs(vals).subs(rho,r_))/v3; v0 = (v0v3.subs(vals).subs(rho,r_))/v3
    V = v3*t**3+v2*t**2+v1*t+v0; U = t**3 + vals[u]*t
    gg = [g2.subs(vals).subs(rho,r_), g1.subs(vals).subs(rho,r_), g0.subs(vals).subs(rho,r_)]
    m = t**9 + 3*vals[u]*t**7 + sum(vals[s_]*t**k for s_,k in ((m6,6),(m5,5),(m4,4),(m3,3),(m2,2),(m1,1),(m0,0)))
    diff = sp.Poly(sp.expand(U**3 + gg[0]*U**2 + gg[1]*U + gg[2] + V**2 - m), t)
    ok = ok and max(abs(sp.N(c,30)) for c in diff.all_coeffs()) < 1e-25
print('all four roots give m = g(U) + V^2:', ok)
import pickle
pickle.dump({'R':R.as_expr(), 'g':(g2,g1,g0)}, open('weier_syms.pkl','wb'))
