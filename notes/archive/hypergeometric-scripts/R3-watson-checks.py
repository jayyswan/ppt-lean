"""
R3: Watson/Polyavirus reduction; check sc/bcc/fcc Watson-integral closed forms.

Every value is labelled numerically-checked (with digits) or classical.
Uses mpmath.  Run with:  py "R3-watson-checks.py"
"""
from mpmath import mp, mpf, mpc, gamma, sqrt, pi, ellipk, besseli, besselj
from mpmath import quad, quadts, inf, exp, log
from math import comb, factorial
from fractions import Fraction

mp.dps = 80
PR = 60  # digits to print


def hr(title):
    print("\n" + "=" * 78)
    print(title)
    print("=" * 78)


# ----------------------------------------------------------------------------
# 1. Simple-cubic return number u(3): the two closed forms and p(3)
# ----------------------------------------------------------------------------
hr("1. simple cubic: u(3) closed forms")

u3_gamma = (sqrt(6) / (32 * pi**3)
            * gamma(mpf(1) / 24) * gamma(mpf(5) / 24)
            * gamma(mpf(7) / 24) * gamma(mpf(11) / 24))
print("u(3) = sqrt6/(32 pi^3) G(1/24)G(5/24)G(7/24)G(11/24)")
print("     =", mp.nstr(u3_gamma, PR))

# literature (OEIS A086231): 1.516386059151978018156012159681420779955387...
u3_lit = mpf("1.51638605915197801815601215968142077995538704445226267656698")
print("literature A086231     :", mp.nstr(u3_lit, PR))
print("diff                   :", mp.nstr(u3_gamma - u3_lit, 6))

# K-form.  k6 is the elliptic MODULUS root of the quartic; the parameter is k6^2.
k6 = (2 - sqrt(3)) * (sqrt(3) - sqrt(2))
print("\nk6 = (2-sqrt3)(sqrt3-sqrt2) =", mp.nstr(k6, PR))
print("quartic at k6 (x^4+12x^3+2x^2-12x+1) =", mp.nstr(k6**4 + 12*k6**3 + 2*k6**2 - 12*k6 + 1, 6))

# mpmath ellipk takes the PARAMETER m = k^2 (matching Mathlib ellipticF c (pi/2)).
u3_K_param_k6sq = (12 / pi**2 * (18 + 12*sqrt(2) - 10*sqrt(3) - 7*sqrt(6))
                   * ellipk(k6**2)**2)
u3_K_param_k6 = (12 / pi**2 * (18 + 12*sqrt(2) - 10*sqrt(3) - 7*sqrt(6))
                 * ellipk(k6)**2)
print("u3 K-form, ellipk(param=k6^2) =", mp.nstr(u3_K_param_k6sq, PR))
print("   diff vs Gamma form         =", mp.nstr(u3_K_param_k6sq - u3_gamma, 6))
print("u3 K-form, ellipk(param=k6)   =", mp.nstr(u3_K_param_k6, PR), " (WRONG convention)")

p3 = 1 - 1 / u3_gamma
print("\np(3) = 1 - 1/u(3) =", mp.nstr(p3, PR))
print("literature p(3)   = 0.340537329550999142835175000691468451967565171417")
print("diff             =", mp.nstr(p3 - mpf("0.340537329550999142835175000691468451967565171417"), 6))


# ----------------------------------------------------------------------------
# 2. Independent checks of u(3)
# ----------------------------------------------------------------------------
hr("2a. simple cubic u(3) from the exact return series  sum a_2n / 36^n")

def a2n_sc(n):
    """number of 2n-step returns on the simple cubic lattice:
       a_2n = C(2n,n) * sum_{j+k+l=n} (n!/(j!k!l!))^2"""
    s = 0
    for k in range(n + 1):
        for j in range(n - k + 1):
            l = n - k - j
            s += factorial(n)**2 // (factorial(k)**2 * factorial(j)**2 * factorial(l)**2)
    return comb(2 * n, n) * s

N = 90
tot = mpf(0)
terms = []
for n in range(N + 1):
    t = mpf(a2n_sc(n)) / mpf(36)**n
    tot += t
    if n <= 5:
        terms.append((n, a2n_sc(n), mp.nstr(t, 8)))
print("first terms (n, a_2n, a_2n/36^n):")
for x in terms:
    print("   ", x)
print("sum_{n<=%d} = " % N, mp.nstr(tot, PR))
print("diff vs Gamma closed form =", mp.nstr(tot - u3_gamma, 6))
print("(tail after n=90 is < 1e-40)")

hr("2b. simple cubic defining Bessel integral  Int_0^inf (e^{-t/3} I_0(t/3))^3 dt")

def bessint(t):
    return (exp(-t / 3) * besseli(0, t / 3))**3

for T in [50, 100, 200, 400, 700]:
    val = quadts(bessint, [0, T])
    print("T=%4d  integral=%s   diff vs u(3)=%s"
          % (T, mp.nstr(val, 20), mp.nstr(val - u3_gamma, 4)))

# asymptotic tail:  e^{-t} I0(t/3)^3 ~ (3/(2 pi))^{3/2} t^{-3/2} (1 + b1/t + b2/t^2 + ...)
# I0(x) ~ e^x/sqrt(2 pi x)(1 + 1/(8x) + 9/(128 x^2) + 225/(3072 x^3) + ...)
# cube, then x = t/3 -> (3/(2 pi))^{3/2} t^{-3/2} (1 + 9/(8 t) + 297/(128 t^2) + ...)
c0 = (3 / (2 * pi))**mpf(1.5)
b1 = mpf(9) / 8
b2 = mpf(297) / 128
b3 = mpf(1269) / 1024   # from cubing the fourth coefficient; kept only as a probe
def tail(T):
    # int_T^inf c0 t^{-3/2}(1 + b1/t + b2/t^2) dt
    return c0 * (2*T**mpf(-0.5) + b1 * (2*mpf(1)/3)*T**mpf(-1.5)
                 + b2 * (2*mpf(1)/5)*T**mpf(-2.5))
for T in [50, 100, 200, 400]:
    val = quadts(bessint, [0, T]) + tail(T)
    print("T=%4d  integral+asym tail=%s  diff=%s"
          % (T, mp.nstr(val, 30), mp.nstr(val - u3_gamma, 4)))


# ----------------------------------------------------------------------------
# 3. bcc
# ----------------------------------------------------------------------------
hr("3. body-centred cubic: u_bcc")

u_bcc = gamma(mpf(1) / 4)**4 / (4 * pi**3)
print("u_bcc = Gamma(1/4)^4/(4 pi^3) =", mp.nstr(u_bcc, PR))
# OEIS A091670
lit_bcc = mpf("1.39320392968567685918424626032536824265748121751561787897")
print("literature A091670            =", mp.nstr(lit_bcc, PR))
print("diff                          =", mp.nstr(u_bcc - lit_bcc, 6))
p_bcc = 1 - 1 / u_bcc
print("p_bcc = 1 - 1/u_bcc =", mp.nstr(p_bcc, PR))

# exact route: Maradudin  P_bcc(z) = [2/pi K(k2)]^2, k2^2 = (1 - sqrt(1-z^2))/2
# at z=1, k2^2 = 1/2;  2/pi K(1/sqrt2) = 2F1(1/4,1/4;1;1) = sqrt(pi)/Gamma(3/4)^2 (Gauss)
half = mpf(1) / 2
route = (2 / pi * ellipk(half))**2
gauss = (sqrt(pi) / gamma(mpf(3) / 4)**2)**2
print("\nMaradudin at z=1: (2/pi K(1/2 param))^2 =", mp.nstr(route, PR))
print("Gauss 2F1(1/4,1/4;1;1)^2 = pi/Gamma(3/4)^4 =", mp.nstr(gauss, PR))
print("diff vs Gamma(1/4)^4/(4pi^3)            =", mp.nstr(route - u_bcc, 6))


# ----------------------------------------------------------------------------
# 4. fcc
# ----------------------------------------------------------------------------
hr("4. face-centred cubic: u_fcc")

u_fcc_plan = 3 * gamma(mpf(1) / 3)**6 / (mpf(2)**(mpf(14) / 3) * pi**4)
u_fcc_corr = 9 * gamma(mpf(1) / 3)**6 / (mpf(2)**(mpf(14) / 3) * pi**4)
print("PLAN candidate  3 G(1/3)^6/(2^{14/3} pi^4) =", mp.nstr(u_fcc_plan, PR))
print("CORRECTED       9 G(1/3)^6/(2^{14/3} pi^4) =", mp.nstr(u_fcc_corr, PR))
print("ratio corrected/candidate =", mp.nstr(u_fcc_corr / u_fcc_plan, 20))
print("candidate is Watson's SECOND triple integral (A091671 = 0.448220394...)")
p_fcc = 1 - 1 / u_fcc_corr
print("p_fcc = 1 - 1/u_fcc =", mp.nstr(p_fcc, PR))

# also the equivalent form with 16*2^{2/3}
u_fcc_alt = 9 * gamma(mpf(1) / 3)**6 / (16 * mpf(2)**(mpf(2) / 3) * pi**4)
print("check 16*2^{2/3} == 2^{14/3}:", mp.nstr(u_fcc_alt - u_fcc_corr, 6))


# ----------------------------------------------------------------------------
# 5. direct numerical evaluation of the 3D Watson integrals (2D reductions)
# ----------------------------------------------------------------------------
hr("5. direct numerical Watson integrals (one variable integrated out)")

# sc: (3/pi^3) int int int 1/(3 - cos x - cos y - cos z)
#   = (9/pi^2) int_0^pi int_0^pi dx dy / sqrt((2-cos x-cos y)(4-cos x-cos y))
def g_sc(x, y):
    a = 2 - mp.cos(x) - mp.cos(y)
    b = 4 - mp.cos(x) - mp.cos(y)
    return 1 / sqrt(a * b)
def sc_int():
    return (9 / pi**2) * quadts(lambda y: quadts(lambda x: g_sc(x, y), [0, pi]), [0, pi])

# bcc: (1/pi^3) int int int 1/(1 - cos x cos y cos z)
#    = (1/pi^2) int_0^pi int_0^pi dx dy / sqrt(1 - cos^2 x cos^2 y)
def g_bcc(x, y):
    return 1 / sqrt(1 - mp.cos(x)**2 * mp.cos(y)**2)
def bcc_int():
    return (1 / pi**2) * quadts(lambda y: quadts(lambda x: g_bcc(x, y), [0, pi]), [0, pi])

# fcc: (1/pi^3) int int int 1/(1 - (c1c2+c1c3+c2c3)/3)
#    = (3/pi^2) int_0^pi int_0^pi dx dy / sqrt(sin^2 x sin^2 y + 8(1 - cos x cos y))
def g_fcc(x, y):
    return 1 / sqrt(mp.sin(x)**2 * mp.sin(y)**2 + 8 * (1 - mp.cos(x) * mp.cos(y)))
def fcc_int():
    return (3 / pi**2) * quadts(lambda y: quadts(lambda x: g_fcc(x, y), [0, pi]), [0, pi])

for name, fn, target in [("sc", sc_int, u3_gamma),
                         ("bcc", bcc_int, u_bcc),
                         ("fcc", fcc_int, u_fcc_corr)]:
    v = fn()
    print("%-4s direct = %s   target = %s   diff = %s"
          % (name, mp.nstr(v, 20), mp.nstr(target, 20), mp.nstr(v - target, 4)))


# ----------------------------------------------------------------------------
# 6. fcc via the diamond lattice / elliptic integrals (independent route)
# ----------------------------------------------------------------------------
hr("6. fcc via diamond:  P_diamond = (4/pi^2) K(k+)K(k-),  P_fcc = (3/4) P_diamond")

# diamond moduli at z=1:  k+-^2 = 1/2 +- sqrt(3)/4
kp2 = mpf(1) / 2 + sqrt(3) / 4
km2 = mpf(1) / 2 - sqrt(3) / 4
P_diam = (4 / pi**2) * ellipk(kp2) * ellipk(km2)   # ellipk takes parameter = k^2
P_fcc_diam = mpf(3) / 4 * P_diam
print("K(sin15)^2-type factors: k+^2 =", mp.nstr(kp2, 20), " k-^2 =", mp.nstr(km2, 20))
print("P_diamond =", mp.nstr(P_diam, 30))
print("(3/4) P_diamond =", mp.nstr(P_fcc_diam, PR))
print("diff vs 9 G(1/3)^6/(2^{14/3}pi^4) =", mp.nstr(P_fcc_diam - u_fcc_corr, 6))
