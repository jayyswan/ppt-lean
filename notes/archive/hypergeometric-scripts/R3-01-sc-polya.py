"""
R3-01: the simple-cubic (Polya) constants u(3) and p(3).

Everything here is numerically checked with mpmath; "classical" marks an identity
taken from the literature.  Run with:  py R3-01-sc-polya.py

Sources:
  Watson, "Three triple integrals", Quart. J. Math. 10 (1939) 266-276.
  Glasser & Zucker, "Extended Watson integrals for the cubic lattices",
    Proc. Nat. Acad. Sci. USA 74 (1977) 1800-1801.
  OEIS A086230 (p(3)), A086231 (u(3)), A091672 (Watson's third integral I_3).
"""
from math import comb, factorial

from mpmath import (mp, mpf, sqrt, pi, gamma, ellipk, besseli, exp, quadts,
                    jtheta, nstr, cos, sin, inf)

mp.dps = 100
OUT = 70


def hr(t):
    print("\n" + "=" * 78)
    print(t)
    print("=" * 78)


def diff(a, b, digits=5):
    return nstr(a - b, digits)


hr("1. u(3): Gamma product, K-form, theta form")

u_gamma = (sqrt(6) / (32 * pi**3)
           * gamma(mpf(1) / 24) * gamma(mpf(5) / 24)
           * gamma(mpf(7) / 24) * gamma(mpf(11) / 24))
print("u(3) = sqrt6/(32 pi^3) G(1/24)G(5/24)G(7/24)G(11/24)")
print("     =", nstr(u_gamma, OUT))

# Greubel's equivalent product (OEIS A086231)
u_greubel = (sqrt(3) - 1) * (gamma(mpf(1) / 24) * gamma(mpf(11) / 24))**2 / (32 * pi**3)
print("(sqrt3-1)(G(1/24)G(11/24))^2/(32 pi^3) =", nstr(u_greubel, OUT))
print("  diff vs Gamma product                  =", diff(u_greubel, u_gamma))

# K-form.  k6 is the elliptic MODULUS; mpmath ellipk takes the PARAMETER m = k^2.
k6 = (2 - sqrt(3)) * (sqrt(3) - sqrt(2))
q = k6**4 + 12 * k6**3 + 2 * k6**2 - 12 * k6 + 1
print("\nk6 = (2-sqrt3)(sqrt3-sqrt2) =", nstr(k6, OUT))
print("quartic x^4+12x^3+2x^2-12x+1 at k6 =", nstr(q, 5))
u_K = 12 / pi**2 * (18 + 12 * sqrt(2) - 10 * sqrt(3) - 7 * sqrt(6)) * ellipk(k6**2)**2
print("K-form, ellipk(param = k6^2)  =", nstr(u_K, OUT))
print("  diff vs Gamma product       =", diff(u_K, u_gamma))

# theta form: u(3) = 3(18+12sqrt2-10sqrt3-7sqrt6) theta_3(0,e^{-pi sqrt6})^4
qth = exp(-pi * sqrt(6))
u_theta = 3 * (18 + 12 * sqrt(2) - 10 * sqrt(3) - 7 * sqrt(6)) * jtheta(3, 0, qth)**4
print("theta_3(0, e^{-pi sqrt6})     =", nstr(jtheta(3, 0, qth), 40))
print("theta form                    =", nstr(u_theta, OUT))
print("  diff vs Gamma product       =", diff(u_theta, u_gamma))

# literature value, OEIS A086231
u_lit = mpf("1.51638605915197801815601215968142077995538704445226267656698")
print("OEIS A086231 (40 digits quoted) diff =", diff(u_gamma, u_lit))


hr("2. p(3) = 1 - 1/u(3)")

p3 = 1 - 1 / u_gamma
print("p(3)           =", nstr(p3, OUT))
p3_lit = mpf("0.340537329550999142826273184432902896710608217124302097763236")
print("OEIS A086230   =", nstr(p3_lit, OUT))
print("diff           =", diff(p3, p3_lit))
# a wrong value that circulates: differs in the 21st digit
p3_bad = mpf("0.340537329550999142835175000691468451967565171417")
print("[caution] 0.340537329550999142835175000691468451967565171417 (bad, differs at d21)")
print("  diff vs correct =", diff(p3, p3_bad))


hr("3. u(3) by the direct triple integral  (3/pi^2) int int 1/sqrt((2-a)(4-a))")

# u(3) = 3 I_3,   I_3 = (1/pi^3) int_0^pi int_0^pi int_0^pi 1/(3-cosx-cosy-cosz).
# Integrating out z:  int_0^pi dz/(3-a-cos z) = pi/sqrt((3-a)^2-1) = pi/sqrt((2-a)(4-a)).
# Use 2 - cos x - cos y = 2 sin^2(x/2) + 2 sin^2(y/2) so there is no 1-cos cancellation.
def sc_integrand(y, x):
    two_minus_a = 2 * sin(x / 2)**2 + 2 * sin(y / 2)**2
    return 1 / sqrt(two_minus_a * (4 - cos(x) - cos(y)))


u_direct = (3 / pi**2) * quadts(lambda y: quadts(lambda x: sc_integrand(y, x), [0, pi]),
                                [0, pi])
print("direct =", nstr(u_direct, 40))
print("  diff vs Gamma product =", diff(u_direct, u_gamma))


hr("4. u(3) from the exact return series  sum_k A002896(k)/36^k   (tail-limited)")

def a2n_sc(n):
    """2n-step return count on the simple cubic lattice (OEIS A002896)."""
    s = 0
    for k in range(n + 1):
        for j in range(n - k + 1):
            l = n - k - j
            s += factorial(n)**2 // (factorial(k)**2 * factorial(j)**2 * factorial(l)**2)
    return comb(2 * n, n) * s


for N in (20, 50, 100):
    tot = sum(mpf(a2n_sc(n)) / mpf(36)**n for n in range(N + 1))
    print("N=%3d partial = %s   diff = %s"
          % (N, nstr(tot, 25), diff(tot, u_gamma, 4)))
print("terms ~ c n^{-3/2}, so a plain partial sum only reaches ~2 digits;")
print("the closed forms (Gamma / K / theta) are the high-precision route.")


hr("5. defining Bessel integral  int_0^inf (e^{-t/3} I_0(t/3))^3 dt  (tail-limited)")

def bessel(t):
    return (exp(-t / 3) * besseli(0, t / 3))**3


# direct quadrature over the whole half-line (mpmath transforms [0,inf])
u_inf = quadts(bessel, [0, inf])
print("quadts [0, inf]      =", nstr(u_inf, 40))
print("  diff vs Gamma product =", diff(u_inf, u_gamma))

# asymptotic tail of e^{-t} I_0(t/3)^3 = c0 t^{-3/2}(1 + b1/t + b2/t^2 + b3/t^3 + ...)
c0 = (3 / (2 * pi))**mpf(1.5)
b = [mpf(9) / 8, mpf(297) / 128, mpf(7587) / 1024]   # cube of the I_0 expansion

def tail(T, order):
    s = mpf(0)
    for j in range(order + 1):
        bj = mpf(1) if j == 0 else b[j - 1]
        s += bj * 2 / (2 * j + 1) * T**(-mpf(2 * j + 1) / 2)
    return c0 * s


for T in (200, 400, 800, 1600):
    raw = quadts(bessel, [0, T])
    print("T=%5d raw = %s  diff=%s" % (T, nstr(raw, 25), diff(raw, u_gamma, 4)))
    for order in (0, 1, 2, 3):
        v = raw + tail(T, order)
        print("        +tail(order %d) = %s  diff=%s" % (order, nstr(v, 30), diff(v, u_gamma, 4)))
print()
print("tail after T is ~ c0*2/sqrt(T) = %s at T=1600" % nstr(c0 * 2 / sqrt(mpf(1600)), 4))

print("\nDONE.")
