"""
R3-03: cross-checks and the modular side.

 * all roots of the quartic x^4 + 12x^3 + 2x^2 - 12x + 1 that defines k6;
 * K at the third singular value, K(sin(pi/12)) = 3^(1/4) Gamma(1/3)^3/(2^(7/3) pi),
   which re-derives I_2 and u_fcc through ellipticF only (no rpow of 2);
 * the identity K((2+sqrt3)/4) = sqrt3 K((2-sqrt3)/4).

Run with:  py R3-03-mods-and-k3.py
"""
from mpmath import (mp, mpf, sqrt, pi, gamma, ellipk, polyroots, sin, cos, nstr)

mp.dps = 70
OUT = 50
S3 = sqrt(3)


def hr(t):
    print("\n" + "=" * 78)
    print(t)
    print("=" * 78)


hr("1. roots of x^4 + 12 x^3 + 2 x^2 - 12 x + 1")

coeffs = [1, 12, 2, -12, 1]
roots = polyroots(coeffs, maxsteps=200, extraprec=200)
for r in roots:
    print("  %s   (value %s)" % (nstr(r, 20), nstr(mp.re(r), 20)))

k6 = (2 - S3) * (S3 - sqrt(2))
print("\nk6 = (2-sqrt3)(sqrt3-sqrt2) = %s" % nstr(k6, OUT))
print("quartic at k6               = %s" % nstr(sum(c * k6**(4 - i) for i, c in enumerate(coeffs)), 5))
# the roots are k6, 1/k6, -k6 - 2 +- ... check the two in (0,1)
pos = [r for r in roots if abs(mp.im(r)) < mpf('1e-40') and 0 < mp.re(r) < 1]
print("roots in (0,1):", [nstr(mp.re(r), 25) for r in pos])


hr("2. K at the third singular value  K(sin(pi/12))")

k3 = sin(pi / 12)
K_k3 = ellipk(k3**2)          # parameter m = k3^2 = (2-sqrt3)/4
K_closed = 3**mpf(0.25) * gamma(mpf(1) / 3)**3 / (2**(mpf(7) / 3) * pi)
print("k3 = sin(pi/12) = (sqrt6-sqrt2)/4 = %s" % nstr(k3, OUT))
print("K(k3^2)                          = %s" % nstr(K_k3, OUT))
print("3^(1/4) Gamma(1/3)^3/(2^(7/3) pi) = %s" % nstr(K_closed, OUT))
print("diff                             = %s" % nstr(K_k3 - K_closed, 5))

i2_via_K3 = S3 * K_closed**2 / pi**2
i2_gamma = 3 * gamma(mpf(1) / 3)**6 / (2**(mpf(14) / 3) * pi**4)
print("\nI_2 = sqrt3 K(k3)^2/pi^2          = %s" % nstr(i2_via_K3, OUT))
print("I_2 = 3 Gamma(1/3)^6/(2^(14/3)pi^4) = %s" % nstr(i2_gamma, OUT))
print("diff                              = %s" % nstr(i2_via_K3 - i2_gamma, 5))
print("u_fcc = 3 I_2                     = %s" % nstr(3 * i2_via_K3, OUT))


hr("3. K((2+sqrt3)/4) = sqrt3 K((2-sqrt3)/4)")

m_minus = (2 - S3) / 4
m_plus = (2 + S3) / 4
print("diff = %s" % nstr(ellipk(m_plus) - S3 * ellipk(m_minus), 5))
print("u_fcc = 3/pi^2 K(m-) K(m+)  = %s"
      % nstr(3 / pi**2 * ellipk(m_minus) * ellipk(m_plus), OUT))
print("u_fcc = 3 sqrt3 K(m-)^2/pi^2 = %s"
      % nstr(3 * S3 * ellipk(m_minus)**2 / pi**2, OUT))

print("\nDONE.")
