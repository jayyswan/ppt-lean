# Z-06: independent re-verification of B2 (decic offset family PGL2-saturation).
# Decic normal form P = u^2 (u'^2 + v'^2) - D^2 v'^2, u cubic (4), v' quadratic (3), D^2 (1).
# Claim: image dimension 7 in the 10-dim space of monic decics (codim 3), and
# PGL2-saturation dimension 9 (codim 1), so the family misses a PGL2-invariant.
import sympy as sp

t = sp.symbols('t')
a0, a1, a2, a3, b0, b1, b2, d2 = sp.symbols('a0 a1 a2 a3 b0 b1 b2 d2')
params = [a0, a1, a2, a3, b0, b1, b2, d2]
u = a0 + a1 * t + a2 * t**2 + a3 * t**3
vp = b0 + b1 * t + b2 * t**2
P = sp.expand(u**2 * (sp.diff(u, t)**2 + vp**2) - d2 * vp**2)
Pp = sp.Poly(P, t)
assert Pp.degree() == 10, Pp.degree()
lead = Pp.LC()
cc = [sp.expand(c / lead) for c in Pp.all_coeffs()[1:11]]   # c9 .. c0 (monic)


def ranks(pt):
    Jimg = sp.Matrix(10, len(params), lambda i, j: sp.diff(cc[i], params[j]).subs(pt))
    Pn = sp.Poly(sp.expand(t**10 + sum(cc[i] * t**(9 - i) for i in range(10))).subs(pt), t)
    Pe = Pn.as_expr()
    n = 10
    T = [sp.Poly(-sp.diff(Pe, t), t),
         sp.Poly(n * Pe - t * sp.diff(Pe, t), t),
         sp.Poly(t**2 * sp.diff(Pe, t) - n * t * Pe, t)]

    def cvec(poly):
        cs = poly.all_coeffs()[1:11]
        cs = cs + [sp.Integer(0)] * (10 - len(cs))
        return cs[:10]
    Tmat = sp.Matrix(10, 3, lambda i, j: cvec(T[j])[i])
    A = sp.Matrix.hstack(Jimg, Tmat)
    return Jimg.rank(), A.rank()


pts = [{a0: 1, a1: 2, a2: -1, a3: 1, b0: 1, b1: 0, b2: 1, d2: 2},
       {a0: 3, a1: -1, a2: 2, a3: 1, b0: -1, b1: 2, b2: 1, d2: 5},
       {a0: 0, a1: 5, a2: 1, a3: -2, b0: 2, b1: -3, b2: 1, d2: 7},
       {a0: 7, a1: 3, a2: -4, a3: 2, b0: 5, b1: 1, b2: -3, d2: 11}]
for k, pt in enumerate(pts):
    r, ra = ranks(pt)
    print(f"point {k}: rank dImage = {r}  rank[dImage|PGL2 orbit] = {ra}  codim = {10-ra}")
