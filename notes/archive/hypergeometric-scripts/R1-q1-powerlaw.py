# R1-Q1: the power_law origin / complete-period question.
#
# Checks (all labels: numerically-checked = NC, classical = CL):
#  (1) V4: int_0^X sqrt(1 + b^2 x^(2b-2)) dx = X * 2F1(-1/2, 1/m; 1+1/m; -b^2 X^m),
#      m = 2b-2, for several rational b.  [NC]
#  (2) The complete-from-zero integral is finite for every b>0 even though the
#      power_law curve is only defined for x>0.                    [NC, structural]
#  (3) Offset first-variation: L_d = L + d * (Delta tangent angle). [NC]
#  (4) The offset length is a PConstructible combination of the already-available
#      difference G(X)-G(x0) and the arctan difference; no new number. [NC + structural]
#  (5) Only the power law (up to a rigid motion) has speed integrand sqrt(1+cx^m):
#      the offset's integrand is explicitly NOT of that form.       [NC]
#
import mpmath as mp
mp.mp.dps = 50

def G(b, X):
    """int_0^X sqrt(1 + b^2 x^(2b-2)) dx, via V4 with m = 2b-2."""
    m = 2*b - 2
    z = -(b**2) * mp.power(X, m)
    return X * mp.hyp2f1(mp.mpf(-1)/2, 1/m, 1 + 1/m, z)

def G_num(b, X):
    f = lambda x: mp.sqrt(1 + b**2 * mp.power(x, 2*b-2))
    return mp.quad(f, [0, 1/mp.mpf(2), 1, X])

print("== (1) V4 power-law arc length: X = 2F1 formula vs numeric integral ==")
for b in [mp.mpf(3)/2, mp.mpf(5)/2, mp.mpf(7)/2, mp.mpf(1)/3, mp.mpf(4), mp.mpf(7)/3]:
    X = mp.mpf('0.9')
    a = G(b, X)
    n = G_num(b, X)
    print(f"  b={float(b):.6f}  m={float(2*b-2):.6f}  diff={mp.nstr(abs(a-n), 5)}  "
          f"2F1={mp.nstr(a, 25)}")

print()
print("== (2) complete-from-zero integral is finite (b>0); the curve still omits x=0 ==")
for b in [mp.mpf(1)/2, mp.mpf(5)/2, mp.mpf(7)/2]:
    val = G(b, 1)  # G(1) is the definite integral from 0 to 1
    print(f"  b={float(b):.3f}: int_0^1 = {mp.nstr(val, 30)} (finite); "
          f"power_law carrier is {{x>0}}")
    # limit value G(X) as X->1 (complete over [0,1])
    print(f"        2F1(-1/2,1/m;1+1/m;-b^2) = "
          f"{mp.nstr(mp.hyp2f1(-mp.mpf(1)/2, 1/(2*b-2), 1+1/(2*b-2), -(b**2)), 30)}")

print()
print("== (3) offset first variation L_d = L + d * (theta(X)-theta(x0)) ==")
b = mp.mpf(5)/2
X = mp.mpf('1.3'); x0 = mp.mpf('0.4'); d = mp.mpf('0.17')
def theta(x):
    return mp.atan(b * mp.power(x, b-1))
def gamma_d(x):
    v = mp.sqrt(1 + b**2 * mp.power(x, 2*b-2))
    yp = b * mp.power(x, b-1)
    nx, ny = -yp/v, 1/v
    return (x + d*nx, mp.power(x, b) + d*ny)
# numeric offset arc length by differentiating gamma_d
def speed_d(x):
    h = mp.mpf('1e-20')
    x1, x2 = gamma_d(x+h), gamma_d(x-h)
    dx = (x1[0]-x2[0])/(2*h); dy = (x1[1]-x2[1])/(2*h)
    return mp.sqrt(dx**2 + dy**2)
Ld_num = mp.quad(speed_d, [x0, (x0+X)/2, X])
Ldiff = G(b, X) - G(b, x0)
pred = Ldiff + d*(theta(X) - theta(x0))
Ld_kappa = mp.quad(lambda x: (1 + d*(b*(b-1)*mp.power(x,b-2)) /
                              mp.power(1+b**2*mp.power(x,2*b-2), mp.mpf(3)/2)) *
                             mp.sqrt(1+b**2*mp.power(x,2*b-2)),
                   [x0, (x0+X)/2, X])
print(f"  L_d numeric      = {mp.nstr(Ld_num, 30)}")
print(f"  L + d*Delta theta= {mp.nstr(pred, 30)}   diff={mp.nstr(abs(Ld_num-pred),5)}")
print(f"  int (1+d*kappa)v = {mp.nstr(Ld_kappa, 30)}   diff={mp.nstr(abs(Ld_num-Ld_kappa),5)}")
print(f"  G(X)-G(x0)       = {mp.nstr(Ldiff, 30)}")

print()
print("== (5) offset speed integrand (as a function of x) is not sqrt(1+c x^m) ==")
def integrand_d(x):  # |gamma_d'(x)| = (1 + d kappa) v
    v = mp.sqrt(1 + b**2*mp.power(x,2*b-2))
    k = b*(b-1)*mp.power(x,b-2)/mp.power(v,3)
    return (1 + d*k)*v
# fit c = (speed_d^2 - 1)/x^m at two points; then compare across the range
for m in [2*b-2]:
    xa, xb = mp.mpf('0.3'), mp.mpf('1.1')
    ca = (integrand_d(xa)**2 - 1)/mp.power(xa, m)
    cb = (integrand_d(xb)**2 - 1)/mp.power(xb, m)
    print(f"  candidate c at x=0.3: {mp.nstr(ca,20)}")
    print(f"  candidate c at x=1.1: {mp.nstr(cb,20)}   (unequal -> not power-law form)")
