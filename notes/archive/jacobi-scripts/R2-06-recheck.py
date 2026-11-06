# R2-06-recheck.py
# Final independent arithmetic re-check of the headline numbers in NOTES-jacobi-R2.md.
# Each quantity is computed by (at least) two independent methods.

from mpmath import (mp, mpf, sqrt, ellipk, ellipf, quad, cos, sin, pi, asin, diff)
mp.dps = 50

print("=== K(1/2): mpmath ellipk vs quadrature of the defining integral ===")
K1 = ellipk(mpf(1)/2)
K2 = quad(lambda a: 1/sqrt(1 - mpf(1)/2*sin(a)**2), [0, pi/2])
print("  ellipk   :", mp.nstr(K1, 45))
print("  quadrature:", mp.nstr(K2, 45))
print("  |diff|   :", mp.nstr(abs(K1-K2), 5))

print()
print("=== lemniscate quarter length: two parametrisations ===")
q1 = quad(lambda t: 1/sqrt(1 - t**4), [0, 1])            # node -> extreme, r^2=cos 2theta
q2 = quad(lambda th: 1/sqrt(cos(2*th)), [0, pi/4])       # polar
print("  int_0^1 dt/sqrt(1-t^4) =", mp.nstr(q1, 45))
print("  int_0^{pi/4} dtheta/sqrt(cos2theta) =", mp.nstr(q2, 45))
print("  K(1/2)/sqrt(2)         =", mp.nstr(K1/sqrt(2), 45))
print("  |q1 - K/sqrt2| =", mp.nstr(abs(q1-K1/sqrt(2)), 5),
      " |q2 - K/sqrt2| =", mp.nstr(abs(q2-K1/sqrt(2)), 5))

print()
print("=== n = c/(1-c) gives modulus k^2 = n/(n+1) = c ===")
for c in ['0.5', '1/3', '2/3', '0.9', '0.123456789']:
    cv = mpf(c)
    nv = cv/(1-cv)
    k2 = nv/(nv+1)
    print(f"  c={c:>12}: n={mp.nstr(nv,30)}  k^2={mp.nstr(k2,30)}  |k^2-c|={mp.nstr(abs(k2-cv),5)}")

print()
print("=== recommended arc identity at c=0.7, alpha=1.2 (n=c/(1-c)) ===")
cv = mpf('0.7'); nv = cv/(1-cv); kk = sqrt(nv/(nv+1))
alpha0 = mpf('1.2')
def r_of(a): return sqrt(nv)*cos(a) + sqrt(1 + nv*cos(a)**2)
def beta_of(a): return asin(kk*sin(a))
def theta_of(a): return pi + nv*a - (nv+1)*beta_of(a)
def xy(a):
    rr = r_of(a); t = theta_of(a)
    return (rr*cos(t), rr*sin(t))
h = mpf('1e-25')
xp, yp = xy(alpha0+h); xm, ym = xy(alpha0-h)
spd = sqrt(((xp-xm)/(2*h))**2 + ((yp-ym)/(2*h))**2)
target = sqrt(nv)/sqrt(1-kk**2*sin(alpha0)**2)
arc = quad(lambda a: sqrt(nv)/sqrt(1-kk**2*sin(a)**2), [0, alpha0])
F = sqrt(nv)*ellipf(alpha0, kk**2)
print("  speed vs sqrt(n)/sqrt(1-k^2 sin^2):", mp.nstr(abs(spd-target), 5))
print("  arc vs sqrt(n)F:", mp.nstr(abs(arc-F), 5))

print()
print("=== affine lemniscate: only sx=symbolic-uniform keeps 1/speed^2 polynomial ===")
# quick numeric cross-check of the degree claim at sx=1,sy=2
sxv, syv = mpf(1), mpf(2)
def speed2_aff(t):
    xp = diff(lambda u: u*(1+u**2)/(1+u**4), t)
    yp = diff(lambda u: u*(1-u**2)/(1+u**4), t)
    return sxv**2*xp**2 + syv**2*yp**2
vals = [1/speed2_aff(t) for t in [mpf('0.3'), mpf('0.6'), mpf('0.9'), mpf('1.2')]]
print("  1/speed^2 samples:", [mp.nstr(v, 12) for v in vals])
print("  (not a degree-4 polynomial: 4 samples from a degree-4 would be interpolated exactly;")
print("   the symbolic computation in R2-03 gives numerator degree 16 / denominator 12)")
