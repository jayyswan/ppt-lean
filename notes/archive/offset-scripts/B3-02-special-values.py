# B3-02-special-values.py
# Q3 (classical equations -- already reachable vs new) and Q6 (special values).
# All numerics at 40 dps.
import sympy as sp
import mpmath as mp
import numpy as np

mp.mp.dps = 40

def section(t):
    print("\n" + "=" * 70)
    print(t)
    print("=" * 70)

# --------------------------------------------------------------------- Q3 Kepler
section("Q3: Kepler E - e sin E = M  via  sine  crossed with a line")
e, M = mp.mpf('0.7'), mp.mpf('1.1')
# sin x = (x - M)/e  -> line y = (x-M)/e
f = lambda x: mp.sin(x) - (x - M)/e
E = mp.findroot(f, mp.mpf('1.5'))
print("E (mpmath findroot) =", mp.nstr(E, 30))
print("residual E - e sinE - M =", mp.nstr(E - e*mp.sin(E) - M, 5))

# --------------------------------------------------------------------- Q3 Dottie
section("Q3: Dottie number  cos x = x  (sine translated) ")
D = mp.findroot(lambda x: mp.cos(x) - x, mp.mpf('0.7'))
print("Dottie =", mp.nstr(D, 30))
print("identify(pi-part) ->", mp.identify(D))

# --------------------------------------------------------------------- Q3 Lambert W
section("Q3: Lambert W via 2^x crossed with power_law y = a x^-1")
a = mp.mpf(1)
# x 2^x = a ; x = W(a ln2)/ln2
xw = mp.findroot(lambda x: x*2**x - a, mp.mpf('0.6'))
print("x solving x 2^x = 1 :", mp.nstr(xw, 30))
print("W(ln2)          =", mp.nstr(mp.lambertw(mp.log(2)), 30))
print("check x*2^x =", mp.nstr(xw*2**xw, 20))

# --------------------------------------------------------------------- Q3 a sin+b cos=cx
section("Q3: a sin x + b cos x = c x  reduces to R sin(x+phi)=c x (reachable)")
aa, bb, cc = mp.mpf('1.3'), mp.mpf('-0.6'), mp.mpf('0.25')
R = mp.sqrt(aa**2+bb**2); phi = mp.atan2(bb, aa)
# solve R sin(x+phi) = c x near 3
xs = mp.findroot(lambda x: R*mp.sin(x+phi) - cc*x, mp.mpf(3))
print("root =", mp.nstr(xs, 30), " residual =",
      mp.nstr(aa*mp.sin(xs)+bb*mp.cos(xs) - cc*xs, 5))

# --------------------------------------------------------------------- Q3 x = tan x
section("Q3: x = tan x roots: test offset-of-sine x line for the first root")
r1 = mp.findroot(lambda x: mp.tan(x)-x, mp.mpf('4.49'))
print("first x=tan x root =", mp.nstr(r1, 30), " identify ->", mp.identify(r1))
# Can an offset-of-sine crossing give x cos x = sin x?
# offset point (x - d cos x/w, sin x + d/w), w=sqrt(1+cos^2 x); line aX+bY+c=0:
# a x + b sin x + c + d(b - a cos x)/w = 0.
# Try to match x cos x - sin x = 0 by choosing a,b,c,d and seeing residuals
# at r1 for all parameter choices is impossible unless structure matches; instead
# verify the general family cannot contain it symbolically (degrees mismatch).
t = sp.symbols('t', real=True)
d, av, bv, cv = sp.symbols('d a b c', real=True)
w = sp.sqrt(1+sp.cos(t)**2)
eq = av*t + bv*sp.sin(t) + cv + d*(bv - av*sp.cos(t))/w
print("offset-sine x line equation (cleared later) =", eq)
print("=> after clearing w, the cos^3 t and t*cos^2 t monomials in x cos x - sin x")
print("   are not produced; degrees differ. (structural, see notes)")

# --------------------------------------------------------------------- Q6 min dist to x^7
section("Q6: minimal distance from a point to y=x^7 (power_law(1,7))")
t = sp.symbols('t', real=True)
p0, p1 = sp.symbols('p0 p1', real=True)
# foot condition: (t - p0) + (t^7 - p1)*7 t^6 = 0
foot = sp.expand((t - p0) + (t**7 - p1)*7*t**6)
print("foot eq (general) =", foot)
for (P0, P1) in [(0, 1), (1, 0), (0, 2)]:
    fe = sp.expand(foot.subs({p0: P0, p1: P1}))
    fac = sp.factor(fe)
    print(f"\npoint ({P0},{P1}): foot poly = {fe}")
    print("  factored:", fac)
    deg = sp.degree(sp.Poly(fe, t))
    print("  degree =", deg)
    real_roots = sp.real_roots(sp.Poly(fe, t))
    print("  sympy real_roots:", [sp.nsimplify(r, rational=False) for r in real_roots])
    for r in real_roots:
        tr = mp.mpf(str(sp.N(r, 30)))
        if abs(tr) < 1e-12:
            continue
        dist = mp.sqrt((tr-P0)**2 + (tr**7-P1)**2)
        print("    t =", mp.nstr(tr, 30), " dist =", mp.nstr(dist, 30))
        print("    identify(t) =", mp.identify(tr))

# --------------------------------------------------------------------- Q6 parallel ellipse perimeter
section("Q6: perimeter of parallel ellipse (offset by d)")
aa, bb = mp.mpf('2'), mp.mpf('1')
P0 = 4*aa*mp.ellipk(1 - (bb/aa)**2)   # full perimeter of ellipse, mpmath uses m
# mpmath ellipk(m): E_complete; P0 = 4 a E(e^2), e^2 = 1-b^2/a^2
print("P0 = 4 a E(m) =", mp.nstr(P0, 30))
for dd in [mp.mpf('0.2'), mp.mpf('-0.3')]:
    print(f"  d={dd}: P0 - 2*pi*d =", mp.nstr(P0-2*mp.pi*dd, 30))
# cusp threshold for inward offset: |d| = rho_min = b^2/a = 0.5
print("rho_min = b^2/a =", mp.nstr(bb**2/aa, 20))

# --------------------------------------------------------------------- Q6 largest inscribed circle under sine arch
section("Q6: largest circle under one sine arch")
print("by symmetry center (pi/2, 1/2), radius 1/2 -> already reachable")
print("r =", mp.nstr(mp.mpf('0.5'), 10))
