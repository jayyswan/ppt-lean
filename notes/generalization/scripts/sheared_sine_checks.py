"""Numerical checks for notes/generalization/SHEARED-SINES.md (labels S1-S7 match the note).
Run: pip install mpmath; python3 sheared_sine_checks.py. Each line prints a residual or a verdict."""
from mpmath import mp, mpf, sin, cos, pi, sqrt, findroot, pslq, chebyt

def findpoly(x, n, maxcoeff):
    """Integer relation among 1, x, ..., x^n (constant term first), or None."""
    return pslq([x**k for k in range(n + 1)], maxcoeff=maxcoeff, maxsteps=10**6)
mp.dps = 150   # well above the ~70 digits a degree-10, height-1e6 relation needs

def show(name, val):
    print(f"{name}: {mp.nstr(val, 5) if not isinstance(val, str) else val}")

# S1  master family: sine graph  x  affine image of the sine graph.
#     A point of the image is (m11 s + m12 sin s + v1, m21 s + m22 sin s + v2); it is on y = sin x iff
#     sin(m11 s + m12 sin s + v1) = m21 s + m22 sin s + v2.
m11, m12, m21, m22, v1, v2 = mpf(1)/2, mpf(3)/5, mpf(1)/7, mpf(-2)/3, mpf(1)/3, mpf(1)/5
g = lambda s: sin(m11*s + m12*sin(s) + v1) - (m21*s + m22*sin(s) + v2)
s0 = findroot(g, 1)
P = (m11*s0 + m12*sin(s0) + v1, m21*s0 + m22*sin(s0) + v2)
show("S1 crossing point lies on y = sin x, residual", abs(P[1] - sin(P[0])))

# S2  level 0 (no shear difference, commensurable frequencies): Engine S of notes/algebraic/C1.md.
#     cos 5t + (1/3) cos 2t + 1/7 = 0  =>  x = cos t is a root of T5 + T2/3 + 1/7 (degree 5).
f = lambda t: cos(5*t) + cos(2*t)/3 + mpf(1)/7
t0 = findroot(f, mpf('0.3'))
x0 = cos(t0)
show("S2 T5(x)+T2(x)/3+1/7 at x = cos t0", abs(chebyt(5, x0) + chebyt(2, x0)/3 + mpf(1)/7))
show("S2 findpoly(cos t0, deg<=6)", str(findpoly(x0, 6, maxcoeff=10**6)))

# S3  level 1 (no shear difference, incommensurable frequencies): sin t = sin(sqrt2 t)/2 + 1/3.
f3 = lambda t: sin(t) - sin(sqrt(2)*t)/2 - mpf(1)/3
t3 = findroot(f3, mpf('0.5'))
show("S3 root t3", t3)
show("S3 findpoly(cos t3, deg<=10, H<=1e6) [None = no relation found]", str(findpoly(cos(t3), 10, maxcoeff=10**6)))

# S4  level 2 (shear difference lambda != 0, commensurable): cos 2t + cos t / 3 + t/5 - 1/7 = 0.
f4 = lambda t: cos(2*t) + cos(t)/3 + t/5 - mpf(1)/7
t4 = findroot(f4, mpf('0.7'))
show("S4 root t4", t4)
show("S4 findpoly(t4, deg<=10)", str(findpoly(t4, 10, maxcoeff=10**6)))
show("S4 findpoly(cos t4, deg<=10)", str(findpoly(cos(t4), 10, maxcoeff=10**6)))

# S5  the rotation-invariance of level 0: replacing t by t + phi (cos phi in the field) keeps the
#     five-term shape. Here phi = pi/3: cos 5(t+phi) etc. expand back into the five-term basis.
phi = pi/3
A, B, C, D, E = mpf(2), mpf(1)/3, mpf(-1)/2, mpf(1)/5, mpf(1)/7
h = lambda t: A*cos(5*t) + B*sin(5*t) + C*cos(2*t) + D*sin(2*t) + E
A2 = A*cos(5*phi) + B*sin(5*phi); B2 = -A*sin(5*phi) + B*cos(5*phi)
C2 = C*cos(2*phi) + D*sin(2*phi); D2 = -C*sin(2*phi) + D*cos(2*phi)
h2 = lambda t: A2*cos(5*t) + B2*sin(5*t) + C2*cos(2*t) + D2*sin(2*t) + E
show("S5 h(t+phi) - h2(t) at t = 0.37", abs(h(mpf('0.37') + phi) - h2(mpf('0.37'))))

# S6  shear orbits of polynomial graphs. A depressed quintic x^5 + a x^3 + b x^2 + c x + d with
#     P-coefficients is an affine image of a RATIONAL poly_graph if I5 = b/|a|^{3/2} is rational
#     (a != 0). Example: a = -sqrt 3, b = r * |a|^{3/2} with r = 2/5; c, d arbitrary.
a = -sqrt(3); r = mpf(2)/5; b = r*abs(a)**mpf(1.5); c = pi/7; d = sqrt(5)
lam = sqrt(abs(a))                     # x-scale
sgn = -1 if a < 0 else 1
base = lambda u: u**5 + sgn*u**3 + r*u**2  # rational poly_graph (r = b/|a|^{3/2} is rational)
target = lambda x: x**5 + a*x**3 + b*x**2 + c*x + d
# image of (u, base(u)) under x = lam u, y = lam^5 * base(u) + c x + d  (scale, then shear, then translate)
err = max(abs(lam**5*base(x/lam) + c*x + d - target(x)) for x in [mpf(-1.3), mpf('0.2'), mpf(2)])
show("S6 quintic: affine image of rational graph matches target", err)
show("S6 I5 = b/|a|^(3/2)", b/abs(a)**mpf(1.5))

# S7  sextic: x^6 + a x^4 + b x^3 + c x^2 + e x + d; invariants I = b/a^{3/2}, K = c/a^2 rational (a > 0).
a = sqrt(2); I = mpf(3)/4; K = mpf(-5)/4
b = I*a**mpf(1.5); c = K*a**2; e = sqrt(11); d = mpf(1)/3
lam = sqrt(a)
base = lambda u: u**6 + u**4 + I*u**3 + K*u**2
target = lambda x: x**6 + a*x**4 + b*x**3 + c*x**2 + e*x + d
err = max(abs(lam**6*base(x/lam) + e*x + d - target(x)) for x in [mpf(-1.3), mpf('0.2'), mpf(2)])
show("S7 sextic: affine image of rational graph matches target", err)
