"""
B2-03-decic-mobius-rank.py  (fast, exact)

The decic offset family (Pptc/Offset.lean normal form)
    P = u^2 (u'^2 + v'^2) - D^2 v'^2,   u cubic, v' quadratic, D^2 = d^2(A^2+B^2)
has image dimension 7 in the 10-dim space of monic decics (codim 3).

Coverage of a target degree-10 polynomial modulo Mobius is governed by the dimension of
the PGL2-saturation of the image, not by codim 3 in coefficient space.  We compute

    rank[ dImage (8 params, rank 7) | orbit tangents (3) ]  at generic rational points.

Rank 10 => the saturation is dominant, i.e. the family covers all moduli after Mobius.

Lie-algebra tangents on a monic degree-n form P:
    translation lambda->lambda+s : -P'
    scaling     lambda->(1+s)lambda : n P - t P'
    inversion   lambda->lambda/(1+s lambda) : t^2 P' - n t P
"""
import sympy as sp

t = sp.symbols('t')
a0,a1,a2,a3,b0,b1,b2,d2 = sp.symbols('a0 a1 a2 a3 b0 b1 b2 d2')
params = [a0,a1,a2,a3,b0,b1,b2,d2]

u  = a0 + a1*t + a2*t**2 + a3*t**3
vp = b0 + b1*t + b2*t**2
expr = sp.expand(u**2*((sp.diff(u,t))**2 + vp**2) - d2*vp**2)

Poly = sp.Poly(expr, t)
assert Poly.degree() == 10
lead = Poly.LC()
cc = [sp.expand(co / lead) for co in Poly.all_coeffs()[1:11]]   # c9..c0

def rank_at(pt):
    Jimg = sp.Matrix(10, len(params),
                     lambda i, j: sp.diff(cc[i], params[j]).subs(pt))
    P = sp.expand(t**10 + sum(cc[i]*t**(9-i) for i in range(10))).subs(pt)
    P = sp.Poly(P, t)
    n = 10
    Pexpr = P.as_expr()
    T = [
        sp.Poly(-sp.diff(Pexpr, t), t),
        sp.Poly(n*Pexpr - t*sp.diff(Pexpr, t), t),
        sp.Poly(t**2*sp.diff(Pexpr, t) - n*t*Pexpr, t),
    ]
    def cvec(poly):
        # coefficients of t^9..t^0 (drop the leading 1), aligned with cc
        cs = poly.all_coeffs()
        cs = cs[1:11]
        cs = cs + [sp.Integer(0)]*(10-len(cs))
        return cs[:10]
    Tmat = sp.Matrix(10, 3, lambda i, j: cvec(T[j])[i])
    A = sp.Matrix.hstack(Jimg, Tmat)
    return Jimg.rank(), A.rank()

for k, pt in enumerate([
    {a0:1, a1:2, a2:-1, a3:1, b0:1, b1:0, b2:1, d2:2},
    {a0:3, a1:-1, a2:2, a3:1, b0:-1, b1:2, b2:1, d2:5},
    {a0:0, a1:5, a2:1, a3:-2, b0:2, b1:-3, b2:1, d2:7},
]):
    r, ra = rank_at(pt)
    print(f"point {k}: rank dImage = {r}, rank [dImage|orbit] = {ra}")
