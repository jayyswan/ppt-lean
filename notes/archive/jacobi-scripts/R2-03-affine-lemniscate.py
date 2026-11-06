# R2-03-affine-lemniscate.py
# Does an affine image of the lemniscate still have first-kind (single-F) arc length?
# Settles whether a single lemniscate base curve + scale_x/scale_y can reach moduli != 1/2.
#
# Lemniscate: x(t)=t(1+t^2)/(1+t^4), y(t)=t(1-t^2)/(1+t^4),  x'^2+y'^2 = 2/(1+t^4).
# Affine image (sx x, sy y): speed^2 = sx^2 x'^2 + sy^2 y'^2.
# Single-F requires 1/speed^2 = Q(t)/const with Q a degree-4 polynomial.

import sympy as sp
from sympy import lambdify
from mpmath import mp, mpf, sqrt, ellipf, quad, cos, sin, pi, asin

t, sx, sy = sp.symbols('t sx sy', real=True)
x = t*(1+t**2)/(1+t**4)
y = t*(1-t**2)/(1+t**4)
xp, yp = sp.diff(x, t), sp.diff(y, t)
speed2 = sp.factor(sx**2 * xp**2 + sy**2 * yp**2)
print("=== affine lemniscate ===")
print("x'^2+y'^2 =", sp.simplify(xp**2 + yp**2))
print("affine speed^2 =", speed2)

print()
print("Special cases: is 1/speed^2 a polynomial?  (single-F iff yes)")
for sxs, sys in [(1, 1), (1, 2), (2, 1), (1, 3), (3, 1), (2, 3)]:
    inv = sp.together(1/speed2.subs({sx: sxs, sy: sys}))
    num, den = sp.fraction(sp.cancel(inv))
    dp = sp.Poly(num, t).degree()
    dq = sp.Poly(den, t).degree()
    print(f"  sx={sxs}, sy={sys}: 1/speed^2 = {sp.factor(inv)}   "
          f"[num deg {dp}, den deg {dq}]  -> polynomial: {dq == 0}")

# --------- numeric: is the affine lemniscate arclength a single F? ---------
# If single-F with modulus k, then s(t0) = (1/A) F(phi(t0),k) for a Moebius phi.
# Test the necessary shape: d/dt [ s(t) ] / [d/dt of F(phi(t),k)] constant.
# Simpler necessary condition: the ratio of successive "quarter periods" is
# that of a single elliptic integral.  We just test the polynomial criterion
# above numerically too, by checking 1/speed^2 at several t and fitting degree<=4.
print()
print("numeric check of polynomial criterion for sx=1,sy=2:")
sxV, syV = mpf(1), mpf(2)
f_expr = 1/speed2.subs({sx: sxV, sy: syV})
f = lambdify(t, f_expr, 'mpmath')
ts = [mpf('0.2'), mpf('0.5'), mpf('0.8'), mpf('1.3')]
for tt in ts:
    print(f"  1/speed^2({tt}) = {mp.nstr(f(tt), 20)}")
print("  (if this is not C*Q(t) for a quartic Q it cannot be a single F)")
