"""
R3-02: the bcc and fcc Watson integrals and lattice return numbers.

Checks the two closed forms claimed in the plan (B5):
   bcc candidate : Gamma(1/4)^4 / (4 pi^3)
   fcc candidate : 3 Gamma(1/3)^6 / (2^(14/3) pi^4)
against the classical Watson triple integrals (Watson 1939; Glasser-Zucker 1977)
and the lattice return numbers (OEIS A091670, A091671, A293237, A293238).

Run with:  py R3-02-bcc-fcc.py
"""
from math import comb

from mpmath import (mp, mpf, sqrt, pi, gamma, ellipk, hyp2f1, quadts, sin, cos,
                    nstr)

mp.dps = 90
OUT = 60
S3 = sqrt(3)


def hr(t):
    print("\n" + "=" * 78)
    print(t)
    print("=" * 78)


def diff(a, b, digits=5):
    return nstr(a - b, digits)


def same(name, a, b, digits=25):
    print("%-40s diff = %s" % (name, diff(a, b, 5)))
    print("    value %s" % nstr(a, digits))


hr("A. Watson I_1  and the bcc return number u_bcc")

i1_gamma = gamma(mpf(1) / 4)**4 / (4 * pi**3)
print("I_1 = Gamma(1/4)^4/(4 pi^3)      =", nstr(i1_gamma, OUT))

# K-form: I_1 = 4 K(1/sqrt2)^2 / pi^2   (K = complete elliptic, parameter = k^2 = 1/2)
i1_K = 4 * ellipk(mpf(1) / 2)**2 / pi**2
same("I_1 == 4 K(param 1/2)^2/pi^2", i1_K, i1_gamma)

# Clausen/hypergeometric: I_1 = 2F1(1/2,1/2;1;1/2)^2
i1_hyp = hyp2f1(mpf(1) / 2, mpf(1) / 2, 1, mpf(1) / 2)**2
same("I_1 == 2F1(1/2,1/2;1;1/2)^2", i1_hyp, i1_gamma)

# direct 2D reduction, cancellation-free:
#   I_1 = (1/pi^2) int_0^pi int_0^pi 1/sqrt(sin^2 x + cos^2 x sin^2 y)
def bcc_int(y, x):
    return 1 / sqrt(sin(x)**2 + cos(x)**2 * sin(y)**2)


i1_direct = (1 / pi**2) * quadts(lambda y: quadts(lambda x: bcc_int(y, x), [0, pi]),
                                 [0, pi])
same("I_1 == direct 2D integral", i1_direct, i1_gamma)

# return series u_bcc = sum_m C(2m,m)^3 / 64^m   (tail-limited)
for N in (30, 60):
    part = sum(mpf(comb(2 * m, m))**3 / mpf(64)**m for m in range(N + 1))
    print("series N=%3d partial = %s  diff = %s"
          % (N, nstr(part, 25), diff(part, i1_gamma, 4)))

u_bcc = i1_gamma
p_bcc = 1 - 1 / u_bcc
print("\nu_bcc = I_1 (bcc return number)   =", nstr(u_bcc, OUT))
print("p_bcc = 1 - 1/u_bcc              =", nstr(p_bcc, OUT))
print("escape prob 1/u_bcc              =", nstr(1 / u_bcc, OUT))
print("OEIS A091670 (u_bcc) = 1.39320392968567685918424626032536824265748121751561787897...")
print("OEIS A293238 (escape)= 0.7177700110461299978211932236657794...")


hr("B. Watson I_2 (the plan's fcc candidate)")

i2_gamma = 3 * gamma(mpf(1) / 3)**6 / (2**(mpf(14) / 3) * pi**4)
print("I_2 = 3 Gamma(1/3)^6/(2^(14/3) pi^4) =", nstr(i2_gamma, OUT))
print("note  2^(14/3) = 16 * 2^(2/3)         =", nstr(16 * 2**(mpf(2) / 3), 20))

# K-form: I_2 = sqrt3 K(sin(pi/12))^2 / pi^2, parameter m = sin^2(pi/12) = (2-sqrt3)/4
m3 = (2 - S3) / 4
i2_K = S3 * ellipk(m3)**2 / pi**2
same("I_2 == sqrt3 K(param (2-sqrt3)/4)^2/pi^2", i2_K, i2_gamma)

# direct 2D reduction (MathWorld eq. 46), cancellation-free
def fcc_int(p, t):
    return 1 / sqrt(cos(t)**2 + mpf(1) / 4 * sin(t)**2 * sin(p)**2)


i2_direct = (1 / pi**2) * quadts(lambda p: quadts(lambda t: fcc_int(p, t), [0, pi / 2]),
                                 [0, pi / 2])
same("I_2 == direct 2D integral", i2_direct, i2_gamma)
print("OEIS A091671 (Watson's 2nd triple integral) = 0.4482203943883814321163854500...")


hr("C. the fcc return number u_fcc  = 3 I_2")

u_fcc = 3 * i2_gamma
print("u_fcc = 3 I_2 = 9 Gamma(1/3)^6/(2^(14/3) pi^4) =", nstr(u_fcc, OUT))
p_fcc = 1 - 1 / u_fcc
print("p_fcc = 1 - 1/u_fcc                            =", nstr(p_fcc, OUT))
print("escape prob 1/u_fcc                            =", nstr(1 / u_fcc, OUT))
print("OEIS A293237 (escape) = 0.74368176349535122890496981936537648...")

# K-product (diamond) form: u_fcc = (3/pi^2) K(m-) K(m+),  m+- = (2 -+ sqrt3)/4
mp_ = (2 + S3) / 4
u_fcc_K = 3 / pi**2 * ellipk(m3) * ellipk(mp_)
same("u_fcc == (3/pi^2) K((2-sqrt3)/4) K((2+sqrt3)/4)", u_fcc_K, u_fcc)

# single-K form: u_fcc = 3 sqrt3 K(m3)^2/pi^2  (equivalent to the above iff K(m+)=sqrt3 K(m-))
u_fcc_K2 = 3 * S3 * ellipk(m3)**2 / pi**2
same("u_fcc == 3 sqrt3 K(param (2-sqrt3)/4)^2/pi^2", u_fcc_K2, u_fcc)
print("identity check K((2+sqrt3)/4) == sqrt3 K((2-sqrt3)/4): diff =",
      diff(ellipk(mp_), S3 * ellipk(m3), 5))

# direct 2D integral for u_fcc = (1/pi^3) int int int 1/(1 - S/3)
u_fcc_direct = 3 * i2_direct
same("u_fcc == 3 * (direct 2D integral)", u_fcc_direct, u_fcc)


hr("D. verdict on the plan's B5 candidates")

print("bcc candidate  Gamma(1/4)^4/(4 pi^3)        : CORRECT")
print("               = I_1 = u_bcc               =", nstr(i1_gamma, 40))
print("fcc candidate  3 Gamma(1/3)^6/(2^(14/3)pi^4): this is I_2, NOT u_fcc")
print("               I_2                         =", nstr(i2_gamma, 40))
print("               u_fcc = 3 I_2               =", nstr(u_fcc, 40))
print("               ratio u_fcc / (plan fcc)    =", nstr(u_fcc / i2_gamma, 20))
print("corrected fcc formula: u_fcc = 9 Gamma(1/3)^6/(2^(14/3) pi^4)")

# literal plan strings
plan_bcc = gamma(mpf(1) / 4)**4 / (4 * pi**3)
plan_fcc = 3 * gamma(mpf(1) / 3)**6 / (2**(mpf(14) / 3) * pi**4)
print("\nplan bcc literal vs u_bcc : diff =", diff(plan_bcc, u_bcc))
print("plan fcc literal vs u_fcc : diff =", diff(plan_fcc, u_fcc))

print("\nDONE.")
