# Z-03b: A3 elimination degree for offset x offset, independent method.
# Groebner basis with lex order over GF(p) (eliminating t2,w1,w2), plus the
# G/H resultant route (which shows the genuine degree-92 factor).
import sys
import sympy as sp

p = int(sys.argv[1]) if len(sys.argv) > 1 else 32003
mode = sys.argv[2] if len(sys.argv) > 2 else 'groebner'

t1, t2, w1, w2 = sp.symbols('t1 t2 w1 w2')
d1, d2 = sp.Integer(1), sp.Integer(1)

g1x = 2 * t1 ** 3 - 3 * t1 ** 2 + 5 * t1 + 7
g1y = t1 ** 3 + 4 * t1 ** 2 - 2 * t1 + 1
g2x = 3 * t2 ** 3 + t2 ** 2 - 4 * t2 + 2
g2y = -t2 ** 3 + 2 * t2 ** 2 + 6 * t2 - 5
u1, v1 = sp.diff(g1x, t1), sp.diff(g1y, t1)
u2, v2 = sp.diff(g2x, t2), sp.diff(g2y, t2)
a, b = g1x - g2x, g1y - g2y
q1, q2 = u1 ** 2 + v1 ** 2, u2 ** 2 + v2 ** 2

E1 = sp.expand(a * w1 * w2 - d1 * v1 * w2 + d2 * v2 * w1)
E2 = sp.expand(b * w1 * w2 + d1 * u1 * w2 - d2 * u2 * w1)
F1 = sp.expand(w1 ** 2 - q1)
F2 = sp.expand(w2 ** 2 - q2)

if mode == 'groebner':
    G = sp.groebner([E1, E2, F1, F2], t2, w1, w2, t1, order='lex', modulus=p)
    print(f"p={p}: Groebner basis size {len(G.polys)}")
    uni = [g for g in G.polys if g.as_expr().free_symbols <= {t1}]
    for g in uni:
        ex = sp.Poly(g.as_expr(), t1, modulus=p)
        print("   univariate in t1: degree", ex.degree())
        fac = sp.factor_list(ex.as_expr(), modulus=p)[1]
        print("   factor degrees:", sorted([(f[0].degree(), f[1]) for f in fac]))
elif mode == 'resultant':
    # G, H as derived: w1 = -d1 J/Q; G = d1^2 J^2 - q1 Q^2;  H = d2^2 v2^2 J^2 - q2 (aJ+v1 Q)^2
    Q = sp.expand(a * u2 + b * v2)
    J = sp.expand(u1 * v2 - v1 * u2)
    Gp = sp.expand(d1 ** 2 * J ** 2 - q1 * Q ** 2)
    Hp = sp.expand(d2 ** 2 * v2 ** 2 * J ** 2 - q2 * (a * J + v1 * Q) ** 2)
    print(f"p={p}: deg_t2 G={sp.Poly(Gp, t2).degree()}, deg_t2 H={sp.Poly(Hp, t2).degree()}")
    Rp = sp.resultant(sp.Poly(Gp, t2), sp.Poly(Hp, t2))
    Rq = sp.Poly(Rp, t1)
    print("   deg_t1 Res(G,H) =", Rq.degree())
    fac = sp.factor_list(Rp, modulus=p)[1]
    print("   factor degrees:", sorted([(sp.Poly(f[0], t1).degree(), f[1]) for f in fac]))
