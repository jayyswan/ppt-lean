# Session 5: every depressed nonic is g(U) + V^2.  Count decompositions, and check that fact 5 = disc(g) = 0.
import sympy as sp, random
t,v3,v2,v1,v0 = sp.symbols('t v3 v2 v1 v0')
def system(m):  # m: list m[k] = coeff of t^k, monic degree 9, m[8]=0
    u1 = sp.Rational(m[7],3)
    U = t**3 + u1*t
    V = v3*t**3+v2*t**2+v1*t+v0
    R = sp.Poly(sum(sp.Integer(m[k])*t**k for k in range(10)) - V**2, t)
    # reduce in base U: R = U^3 + g2 U^2 + g1 U + g0 ; solve g's from t^6,t^3,t^0 then conditions t^5,t^4,t^2,t^1
    g2,g1,g0 = sp.symbols('g2 g1 g0')
    D = sp.Poly(sp.expand(R.as_expr() - (U**3+g2*U**2+g1*U+g0)), t)
    c = {k: D.coeff_monomial(t**k) for k in range(10)}
    s2 = sp.solve(c[6], g2)[0]; s1 = sp.solve(c[3].subs(g2,s2), g1)[0]; s0 = sp.solve(c[0], g0)[0]
    eqs = [sp.expand(c[k].subs({g2:s2,g1:s1})) for k in (5,4,2,1)]
    assert sp.expand(c[7])==0 and sp.expand(c[8])==0
    return eqs,(s2,s1,s0)
random.seed(5)
for trial in range(3):
    m = [random.randint(-5,5) for _ in range(8)]+[0,1]
    eqs,gs = system(m)
    G = sp.groebner(eqs, v0,v1,v2,v3, order='lex')
    last = sp.Poly(G.exprs[-1], v3)
    print('nonic coeffs', m, '| eliminant in v3: degree', last.degree(), '| even:', all(e[0]%2==0 for e in last.monoms()))
    # eliminant for disc(g)
    X = sp.symbols('X'); g = X**3+gs[0]*X**2+gs[1]*X+gs[2]
    print('   factor degrees of v3-eliminant:', [f.degree() for f,_ in sp.Poly(last,v3).factor_list()[1]])
