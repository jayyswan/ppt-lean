"""
R1b step 4: pole-at-infinity for the unbounded bases, and the exactness loophole.

(1) poly_graph y=p(x), deg d:  ds=sqrt(1+p'(x)^2) dx ~ |lead(p')| x^{d-1} dx.
    On the hyperelliptic curve y^2 = 1+p'(x)^2 (P of degree 2(d-1)), at infinity
    the first-kind differential is dx/y; ds = P dx/y. In the local coordinate w:
      P even degree 2g+2: w=1/x, P ~ p t^{2(d-1)}, ds ~ (lead sqrt) u^{-(d+1)} du, order d+1.
(2) y=x^3: ds = (2/3) dx/y + d[x sqrt(1+9x^4)/3]  -> second-kind part is EXACT.
    But ds is not first kind; the exact part cannot be removed because ds has a
    pole at infinity of order 4 while (alpha+beta x)dx/y is holomorphic there.
(3) power_law b=5/2: cubic curve, p=3 odd; at the branch point infinity the first
    kind form is holomorphic but ds has an order-6 pole.
(4) Bounded sub-arc of an unbounded curve: restricting x to a window changes the
    domain of integration, not the differential class; the pole is still there.
    Verify numerically that the *differential* (not the integral over a finite
    window) has the same leading behaviour regardless of how we `restrict`.
"""
import sympy as sp
from mpmath import mp, mpf, sqrt, quad
mp.dps = 30

x, w = sp.symbols('x', positive=True), sp.symbols('w', positive=True)

# (1) degree-6 graph
p = x**6
P = sp.expand(1 + sp.diff(p, x)**2)
print("y=x^6: 1+p'^2 =", P, " (degree", sp.degree(P), ")")
# ds = sqrt(P) dx ; leading behaviour
lead = sp.limit(sp.sqrt(P)/x**5, x, sp.oo)
print("  sqrt(P) ~", lead, "*x^5 ; ds ~", lead, "x^5 dx")
# local coordinate of y^2=P at infinity (deg P=10, even => genus 4), w=1/x, dx=-dw/w^2
print("  ds = y dx ; with w=1/x, ds ~ -", lead, "w^{-7} dw (order 7, second kind)")

# degree-2 graph (parabola) for contrast: ds elementary, pole is exact
p2 = x**2
print("\ny=x^2: sqrt(1+4x^2)dx = d[ x sqrt(1+4x^2)/2 + asinh(2x)/4 ] (elementary; genus 0)")

# (2) cubic graph, exact second-kind part
print("\ny=x^3 recheck (symbolic residual, must be 0):")
res = sp.simplify(sp.diff(x*sp.sqrt(1+9*x**4)/3, x) + sp.Rational(2,3)/sp.sqrt(1+9*x**4)
                  - sp.sqrt(1+9*x**4))
print("  ", res)
print("  first-kind coefficient 2/3 != 0 ; boundary term coefficient 1/3 != 0")

# (3) power_law b=5/2
k = sp.symbols('k', positive=True)
P3 = 1 + k*x**3
lead3 = sp.limit(sp.sqrt(P3)/x**sp.Rational(3,2), x, sp.oo)
print("\npower_law b=5/2: sqrt(1+k x^3) ~", lead3, "x^{3/2}")
print("  local coordinate at branch point: x=1/w^2, y=1/w^3, dx=-2/w^3 dw")
print("  ds = y dx ~ -2 w^{-6} dw (order 6, second kind); first-kind dx/y ~ -2 dw (holomorphic)")

# (4) numeric: the differential tail is scale-independent
#     int_N^{2N} sqrt(1+9x^4) dx  ~ (3/5)( (2N)^5 - N^5 ) ; ratio to N^5 -> const
for N in [mpf(10), mpf(100), mpf(1000)]:
    val = quad(lambda u: sqrt(1+9*u**4), [N, 2*N])
    print(f"  N={float(N):7.0f}  int_N^2N sqrt(1+9x^4) / N^3 = {mp.nstr(val/N**3, 12)}")
print("  tail ~ (2^3-1) N^3 = 7 N^3 (sqrt(1+9x^4)~3x^2), independent of any domain restriction")

# Verify the claimed leading coefficient of the exact-boundary decomposition numerically
# (the same for any window [a,b]: s(b)-s(a) = boundary difference + (2/3)(I(b)-I(a)))
a, b = mpf('0.3'), mpf('2.7')
sb = quad(lambda u: sqrt(1+9*u**4), [0, b]) - quad(lambda u: sqrt(1+9*u**4), [0, a])
Ib = quad(lambda u: 1/sqrt(1+9*u**4), [0, b]) - quad(lambda u: 1/sqrt(1+9*u**4), [0, a])
bnd = b*sqrt(1+9*b**4)/3 - a*sqrt(1+9*a**4)/3
print("  window [0.3,2.7] residual:", mp.nstr(sb - (bnd + mpf(2)/3*Ib), 5))
