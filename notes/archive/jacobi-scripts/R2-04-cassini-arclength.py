# R2-04-cassini-arclength.py
# Is the Euclidean arc length of a general Cassini oval elliptic or hyperelliptic?
# Derived: quarter perimeter from the outer vertex (u=r^2 from alpha0=a^2+b^2 down to
# beta0=|a^2-b^2|) is
#     J = (b^2/sqrt(alpha0)) * int_0^{pi/2} (1 - k^2 sin^2 phi)^{-1/4} dphi,
#     k = 2ab/(a^2+b^2),  k^2 = 1-(beta0/alpha0)^2,
# i.e. exponent -1/4, a hyperelliptic (superelliptic) integral, NOT elliptic.
# We check this numerically against the direct quadrature of ds/dtheta.

from mpmath import mp, mpf, sqrt, quad, cos, sin, pi, asin

mp.dps = 30

def quarter_perimeter(aval, bval):
    av, bv = mpf(aval), mpf(bval)
    a2, b2 = av*av, bv*bv
    def r2(th):
        return a2*cos(2*th) + sqrt(b2*b2 - a2*a2*sin(2*th)**2)
    def r(th):
        return sqrt(r2(th))
    def integrand(th):
        h = mpf('1e-18')
        dr = (r(th+h)-r(th-h))/(2*h)
        return sqrt(r(th)**2 + dr**2)
    direct = quad(integrand, [0, pi/2])
    alpha0, beta0 = a2+b2, abs(a2-b2)
    k = 2*av*bv/(a2+b2)
    # exponent -1/4 integral
    hyper = quad(lambda ph: (1 - k**2*sin(ph)**2)**mpf('-0.25'), [0, pi/2])
    pred = (b2/sqrt(alpha0))*hyper
    # elliptic guess with exponent -1/2 (what a first-kind integral would give)
    ell = quad(lambda ph: (1 - k**2*sin(ph)**2)**mpf('-0.5'), [0, pi/2])
    pred_ell = (b2/sqrt(alpha0))*ell
    return direct, pred, pred_ell, k

print("=== Cassini quarter perimeter: hyperelliptic (-1/4) vs elliptic (-1/2) ===")
for av, bv in [(mpf(1), mpf(2)), (mpf(1), mpf(3)), (mpf(1), mpf('1.5')),
               (mpf(1), mpf(10)), (mpf(2), mpf(3))]:
    direct, pred, pred_ell, k = quarter_perimeter(av, bv)
    print(f"a={mp.nstr(av,4)}, b={mp.nstr(bv,6)} (k={mp.nstr(k,12)}):")
    print(f"   direct       = {mp.nstr(direct,20)}")
    print(f"   -1/4 pred    = {mp.nstr(pred,20)}   diff {mp.nstr(abs(direct-pred),4)}")
    print(f"   -1/2 (elliptic guess) = {mp.nstr(pred_ell,20)}  diff {mp.nstr(abs(direct-pred_ell),4)}")

# special lemniscate a=b: topology changes (beta0=0), handle separately
print()
print("=== lemniscate a=b=1 (degenerate, elliptic) ===")
mp.dps = 25
def lemn_quarter():
    # r^2 = cos 2t, ds = dt/sqrt(cos 2t)
    return quad(lambda t: 1/sqrt(cos(2*t)), [0, pi/4])
from mpmath import ellipk
print("quarter lemniscate length =", mp.nstr(lemn_quarter(), 20))
print("sqrt(2)/2 * K(1/2)      =", mp.nstr(sqrt(2)/2*ellipk(mpf(1)/2), 20))
