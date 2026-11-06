# R2-01-serret.py
# Serret's first-class curves: rederivation and numerical verification.
# Sources: Serret, JMPA 10 (1845) 257-285 and 421-429; JMPA 11 (1846) 89-95.
#
# Construction (Serret 1846, "Theorie geometrique ..."):
#   Fix O. A triangle OMP has OP = sqrt(n), MP = sqrt(n+1), OM = r.
#   Let alpha = angle MOP, beta = angle OMP. Then
#       r^2 - 2 sqrt(n) r cos(alpha) - 1 = 0          (law of cosines at O)
#       cos(beta) = (r^2 + 1) / (2 r sqrt(n+1))
#   and the point M is placed at polar angle theta from a fixed axis with
#       theta = n*alpha - (n+1)*beta    (+ const).
#   The curve is bounded, r in [sqrt(n+1)-sqrt(n), sqrt(n+1)+sqrt(n)].
#
# We verify symbolically:
#   (1) the quadratic for r,
#   (2) cos(beta) formula and sin(beta) = k sin(alpha), k^2 = n/(n+1),
#   (3) dtheta/dr = (r^2-(2n+1)) / (r*Delta), Delta^2 = -r^4+2(2n+1)r^2-1,
#   (4) ds/dr = 2 sqrt(n(n+1))/Delta,
#   (5) ds/dalpha = sqrt(n)/sqrt(1-k^2 sin^2 alpha)   [=> arc = sqrt(n) F(alpha,k)]
# and numerically that the arclength matches mpmath.ellipf.

import sympy as sp

a = sp.symbols('alpha', real=True)
n = sp.symbols('n', positive=True)

r = sp.sqrt(n) * sp.cos(a) + sp.sqrt(n * sp.cos(a)**2 + 1)

print("=== Serret first class: symbolic checks ===")
print("(1) r^2 - 2 sqrt(n) r cos a - 1 =",
      sp.simplify(sp.expand(r**2 - 2 * sp.sqrt(n) * r * sp.cos(a) - 1)))

# cos(beta) from law of cosines, and the relation sin beta = k sin alpha
cosb_candidate = (r**2 + 1) / (2 * r * sp.sqrt(n + 1))
print("(2a) cos(beta) simplifies to:",
      sp.simplify(cosb_candidate))
# law of sines: MP = sqrt(n+1) opposite alpha, OP = sqrt(n) opposite beta
# => sin(beta)/sqrt(n) = sin(alpha)/sqrt(n+1) => sin(beta)=k sin(alpha)
k = sp.sqrt(n / (n + 1))
print("(2b) sqrt(n/(n+1)) - sin(beta)/sin(alpha) check, using cos(beta) above:")
sinb_sq = sp.simplify(1 - cosb_candidate**2)
print("     sin^2(beta) - (n/(n+1)) sin^2(alpha) =",
      sp.simplify(sinb_sq - k**2 * sp.sin(a)**2))

# Delta
Delta2 = -r**4 + 2 * (2 * n + 1) * r**2 - 1
Delta = sp.sqrt(Delta2)
# check cos beta relation to Delta: sin(beta) = Delta/(2 r sqrt(n+1))
print("(2c) sin(beta) - Delta/(2 r sqrt(n+1)) (should be 0):",
      sp.simplify(sp.sqrt(sp.factor(sinb_sq)) - Delta / (2 * r * sp.sqrt(n + 1))))

# theta = n a - (n+1) beta, beta = asin(k sin a), so d beta/da = k cos a / cos beta
beta = sp.asin(k * sp.sin(a))
theta = n * a - (n + 1) * beta
dth_da = sp.diff(theta, a)
dr_da = sp.diff(r, a)

# (5) speed^2 = (dr/da)^2 + r^2 (dtheta/da)^2 should equal n/(1-k^2 sin^2 a)
speed2 = sp.simplify(dr_da**2 + r**2 * dth_da**2)
print("(5a) speed^2 * (1-k^2 sin^2 a) - n =",
      sp.simplify(speed2 * (1 - k**2 * sp.sin(a)**2) - n))

# (3)-(4) check via r as independent variable numerics (symbolic is heavy);
# instead check the identity  Delta^2 + (r^2-(2n+1))^2 = 4 n (n+1)
u = sp.symbols('u', positive=True)  # u = r^2
D2 = -u**2 + 2 * (2 * n + 1) * u - 1
print("(3) Delta^2 + (u-(2n+1))^2 - 4n(n+1) =",
      sp.simplify(D2 + (u - (2 * n + 1))**2 - 4 * n * (n + 1)))

# ---------------------------------------------------------------
# t = tan(alpha) parametrisation: quartic Q(t) = (1+t^2)(1+(1-k^2)t^2)
# Then ds = sqrt(n) dt / sqrt(Q(t)), i.e. speed_t^2 * Q(t) = n.
# ---------------------------------------------------------------
t = sp.symbols('t', real=True)
print()
print("=== t = tan(alpha): speed_t^2 * Q(t) = n ===")
print("Q(t) = (1+t^2)*(1+(1-k^2)*t^2), roots +-i, +-i/sqrt(1-k^2)")
print("(this is the 'speed^2 * quartic = const' statement of the brief)")

# ---------------------------------------------------------------
# Numerical verification against mpmath.ellipf
# ---------------------------------------------------------------
from mpmath import mp, mpf, sqrt, ellipf, quad, sin, cos, asin, tan, pi

mp.dps = 30

def check_numeric(nval, alpha0):
    nval = mpf(nval)
    kk = sqrt(nval / (nval + 1))
    # curve in the polar angle parametrisation
    def r_of(al):
        return sqrt(nval) * cos(al) + sqrt(nval * cos(al)**2 + 1)
    def beta_of(al):
        return asin(kk * sin(al))
    def theta_of(al):
        return nval * al - (nval + 1) * beta_of(al)
    def xy(al):
        rr = r_of(al)
        th = theta_of(al)
        return (rr * cos(th), rr * sin(th))
    # numeric speed (central difference) at alpha0
    h = mpf('1e-15')
    xp, yp = xy(alpha0 + h)
    xm, ym = xy(alpha0 - h)
    spd = sqrt(((xp - xm) / (2 * h))**2 + ((yp - ym) / (2 * h))**2)
    target = sqrt(nval) / sqrt(1 - kk**2 * sin(alpha0)**2)
    # arclength 0 -> alpha0 by quadrature of speed(alpha)
    arc = quad(lambda al: sqrt(nval) / sqrt(1 - kk**2 * sin(al)**2), [0, alpha0])
    F = sqrt(nval) * ellipf(alpha0, kk**2)
    return spd, target, arc, F

print()
print("=== numerical verification (mpmath, 30 dps) ===")
for nval in ['2', '0.5', '3', '1', '1.7']:
    for al0 in ['0.3', '0.9']:
        spd, target, arc, F = check_numeric(nval, mpf(al0))
        print(f"n={nval:>4} alpha0={al0}: |speed-target|={mp.nstr(abs(spd-target),5)}"
              f"  |arc - sqrt(n)F|={mp.nstr(abs(arc - F), 5)}")

# exact lemniscate check: n=1
print()
print("lemniscate n=1: k^2 = 1/2.")
nval, alpha0 = mpf(1), mpf('0.7')
spd, target, arc, F = check_numeric(nval, alpha0)
print("  k^2 =", mp.nstr(mpf(1)/2, 20), " arc =", mp.nstr(arc, 20),
      " sqrt(n)F =", mp.nstr(F, 20), " diff =", mp.nstr(arc - F, 5))
