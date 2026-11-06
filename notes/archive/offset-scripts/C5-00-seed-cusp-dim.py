# C5-00-seed-cusp-dim.py
# Seed computation for PLAN-offset-C5 (cusp extraction as a candidate Defs primitive).
#
# Effective dimension of the cubic-pair cusp / curvature family
#   (x'y'' - y'x'')^2 d^2 - (x'^2 + y'^2)^3 = 0,   degree 12 in t,
# as a family of degree-12 binary forms in the 9 parameters (cubic pair + d).
# Compares against the 9 moduli of a full degree-12 binary form up to GL2.
#
# Run: C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe C5-00-seed-cusp-dim.py
#
# Result (random rational point, seed 7):
#   coeff Jacobian rank 6 / 9 ; monic rank 5 ; + sl2 saturation rank 7.
# => codimension >= 2 in degree-12 moduli: the cusp family is NOT dominant,
#    so cusp extraction alone cannot cover degree 12.

import random

import sympy as sp

t = sp.symbols("t")
a0, a1, a2, a3, b0, b1, b2, b3, d = sp.symbols("a0 a1 a2 a3 b0 b1 b2 b3 d")
params = [a0, a1, a2, a3, b0, b1, b2, b3, d]

x = a3 * t**3 + a2 * t**2 + a1 * t + a0
y = b3 * t**3 + b2 * t**2 + b1 * t + b0
xp, yp = sp.diff(x, t), sp.diff(y, t)
xpp, ypp = sp.diff(xp, t), sp.diff(yp, t)
W = xp * ypp - yp * xpp
q = xp**2 + yp**2
F = sp.expand(W**2 * d**2 - q**3)
poly = sp.Poly(F, t)
print("degree in t:", poly.degree())

coeffs = [poly.coeff_monomial(t**k) for k in range(poly.degree() + 1)]
J = sp.Matrix([[sp.diff(c, p) for p in params] for c in coeffs])

random.seed(7)
pt = {p: sp.Rational(random.randint(1, 9)) for p in params}
Jv = J.subs(pt)
print("coeff Jacobian shape:", Jv.shape, "rank:", Jv.rank())

# Monic-normalised map: coefficients divided by the leading coefficient (up to scale).
lead = coeffs[-1]
monic = [sp.simplify(c / lead) for c in coeffs]
Jm = sp.Matrix([[sp.diff(c, p) for p in params] for c in monic])
Jmv = Jm.subs(pt)
print("monic (up to scale) rank:", Jmv.rank())


# mod-PGL2 saturation: add the infinitesimal sl2 generators on the root variable,
# t -> t + e*(alpha t^2 + beta t + gamma).
def sl2_cols():
    gamma = sp.Matrix([coeffs[k] * k if k >= 1 else 0 for k in range(len(coeffs))])
    beta = sp.Matrix([coeffs[k] * (k - 1) for k in range(len(coeffs))])
    alpha = sp.Matrix([(k - 2) * coeffs[k - 1] if k >= 1 else 0 for k in range(len(coeffs))])
    return gamma.subs(pt), beta.subs(pt), alpha.subs(pt)


g, bt, al = sl2_cols()
Aug = Jv.row_join(g).row_join(bt).row_join(al)
print("coeff Jacobian + sl2 saturation rank:", Aug.rank())

Augm = Jmv.row_join(g).row_join(bt).row_join(al)
print("monic + sl2 saturation rank:", Augm.rank())
