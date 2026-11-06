import sympy as sp

X, Y, d, t = sp.symbols('X Y d t')

def offset_implicit(x, y, t, d, X, Y):
    xp = sp.diff(x, t); yp = sp.diff(y, t)
    E1 = (X - x)**2 + (Y - y)**2 - d**2
    E2 = (X - x)*xp + (Y - y)*yp
    # clear denominators
    den = sp.denom(sp.together(E1)); 
    E1p = sp.together(E1); E2p = sp.together(E2)
    E1n = sp.numer(E1p); E2n = sp.numer(E2p)
    R = sp.resultant(E1n, E2n, t)
    R = sp.factor(R)
    return R

def report(name, x, y, dval=None):
    print("="*70)
    print(name)
    dd = d if dval is None else dval
    R = offset_implicit(x, y, t, dd, X, Y)
    print("resultant factored:")
    print(R)
    P = sp.Poly(R, X, Y)
    print("total degree in X,Y:", P.total_degree())
    for f, m in sp.factor_list(R)[1]:
        Pf = sp.Poly(f, X, Y)
        print("  factor mult", m, "degree", Pf.total_degree(), ":", sp.factor(f)[:0] if False else f)

# parabola y = t^2
report("parabola (t, t^2)", t, t**2)
