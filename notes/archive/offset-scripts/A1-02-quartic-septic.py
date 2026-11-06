import sympy as sp

t, X, d = sp.symbols('t X d')

def analyze_graph(p, dval, label):
    print("="*72)
    print(label)
    p = sp.expand(p)
    pp = sp.diff(p, t)
    # crossing poly with line Y=0 (x-axis): p(t)^2 * (1 + p'^2) - d^2
    P = sp.expand(p**2 * (1 + pp**2) - dval**2)
    Ppoly = sp.Poly(P, t)
    print("crossing poly degree =", Ppoly.degree())
    print("leading coeff =", Ppoly.LC())
    fl = sp.factor_list(P, t)
    print("factor_list over QQ:", [(str(f), m, sp.Poly(f,t).degree()) for f,m in fl[1]])
    # recovery poly Q(z) = (X - z) - p(z) p'(z); we insert X later
    # minimal poly of X = t + p p' by elimination
    R = sp.resultant(P, X - (t + p*pp), t)
    R = sp.factor(R)
    print("X = t + p p' resultant (factored):")
    print(R)
    print("degree in X:", sp.Poly(R, X).degree())

# quartic graph
analyze_graph(t**4 + t + 1, 1, "quartic p = t^4 + t + 1, d=1")
