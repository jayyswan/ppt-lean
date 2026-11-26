"""Numerical checks for notes/generalization/SHEARED-SINES.md (labels S1-S8 match the note).
Run: pip install mpmath; python3 sheared_sine_checks.py. Each line prints a residual or a verdict."""
from mpmath import mp, mpf, sin, cos, pi, sqrt, findroot, pslq, chebyt

def findpoly(x, n, maxcoeff):
    """Integer relation among 1, x, ..., x^n (constant term first), or None.
    A relation of degree <= 10 and height <= 1e6 needs about 70 digits; we work at 150."""
    return pslq([x**k for k in range(n + 1)], maxcoeff=maxcoeff, maxsteps=10**6)
mp.dps = 150

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

# S6  master formula for sheared graphs: the affine image (x, y) -> M (x, y) of the graph (t, g(t)) has
#     speed |z2| * |g'(t) - r| with z1 = m11 + i m21, z2 = m12 + i m22, r = -z1/z2.
from mpmath import mpc, diff, exp, log, quad, ellipe, ellipf, ellippi, atan, findroot as _fr
M = (mpf(1)/2, mpf(-3)/5, mpf(2)/7, mpf(4)/3)          # m11, m12, m21, m22
z1 = mpc(M[0], M[2]); z2 = mpc(M[1], M[3]); r = -z1/z2
for name, g in [("sin", sin), ("2^x", lambda t: 2**t), ("x^(5/2)", lambda t: t**mpf(2.5))]:
    t = mpf('0.83')
    X = lambda s: M[0]*s + M[1]*g(s); Y = lambda s: M[2]*s + M[3]*g(s)
    sp = sqrt(diff(X, t)**2 + diff(Y, t)**2)
    show(f"S6 speed of sheared {name} - |z2||g'-r|", abs(sp - abs(z2)*abs(diff(g, t) - r)))

# S7  the sine instance is the third-kind family of ThirdKindAll/Circular.lean. Given r = b + i a
#     (b >= 0, a > 0), the (n, c) of sheared-sine-inversion.md S1, and the antiderivative circG there,
#     the arc length int_0^{T(th)} |cos t - r| dt equals circG(c, n, th).
a, b = mpf(7)/10, mpf(9)/10
S = sqrt((1 + a**2 + b**2)**2 - 4*b**2)
n = -(1 + a**2 + b**2 - S)/(2*S); c = (1 - a**2 - b**2 + S)/(2*S); Dd = c - n
show("S7 a from (n,c)  [Circular: sqrt(c(1-c))/(c-n)]", abs(sqrt(c*(1-c))/Dd - a))
show("S7 b from (n,c)  [Circular: sqrt((1-n)(-n))/(c-n)]", abs(sqrt((1-n)*(-n))/Dd - b))
p, q = sqrt(1-n), sqrt(-n); k = p - q
th = mpf('1.1')
T = 2*atan(k*mp.tan(th/2))
L = quad(lambda t: abs(cos(t) - mpc(b, a)), [0, T])
Dl = sqrt(1 - c*sin(th)**2); W = 1 - n*sin(th)**2
elem = -n*sin(th)*cos(th)*Dl/W - p*q*(sin(th)*Dl/W + atan(sqrt(Dd)*sin(th)/Dl)/sqrt(Dd))
G = (ellipe(th, c) - ellipf(th, c) + (1-n)*ellippi(n, th, c) + elem)/sqrt(Dd)
show("S7 int_0^T |cos t - r| - circG(c,n,theta)", abs(L - G))

# S8  inversion (the new direction): lay sigma = 1 along the sheared sine with r = b + i a and read t1.
sigma = mpf(1)
t1 = _fr(lambda u: quad(lambda t: abs(cos(t) - mpc(b, a)), [0, u]) - sigma, mpf(1))
show("S8 t1 = Lambda_r^{-1}(1)", t1)
show("S8 findpoly(t1, deg<=8) [None = no relation]", str(findpoly(t1, 8, maxcoeff=10**5)))
