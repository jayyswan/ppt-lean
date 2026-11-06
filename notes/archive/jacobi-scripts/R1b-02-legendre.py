"""
R1b step 1 (cont.): Legendre reduction of the two elliptic power-law families.

Family P=4  (n = 2b-2 = 4Q': b=3 is Q'=1): first-kind part  I4(x)=int dt/sqrt(1+k t^4).
Family P=3  (n = 3Q': b=5/2 is Q'=1):       first-kind part  I3(x)=int dt/sqrt(1+k t^3).

Curves y^2 = 1 + k t^4  (j=1728) and y^2 = 1 + k t^3  (j=0).
Compute the Legendre modulus from the cross-ratio of roots (sympy, exact), and
verify numerically with mpmath that the inverse amplitude is a Moebius function.
"""
import sympy as sp
from mpmath import mp, mpf, sqrt, quad, ellipf, ellipk, ellipfun, findroot, log

mp.dps = 30

# ---------- cross-ratio / j-invariant ----------
def j_from_quartic(coeffs, var):
    roots = sp.Poly(coeffs, var).all_roots()
    e = [complex(r) for r in roots]
    # order by angle then magnitude for a stable cross-ratio
    e = sorted(e, key=lambda z: (round(__import__('math').atan2(z.imag, z.real), 9), abs(z)))
    a, b, c, d = e
    lam = ((a - b) * (c - d)) / ((a - c) * (b - d))
    return sp.nsimplify(sp.re(lam), rational=False), lam

t = sp.symbols('t')
for k in [1, 9, sp.Rational(25, 4), 7]:
    R = 1 + k * t**4
    lamR, lam = j_from_quartic(R, t)
    j = 256 * (1 - lam + lam**2)**3 / (lam**2 * (1 - lam)**2)
    print(f"quartic 1+{k} t^4 : lambda(approx)={sp.N(lam,12)}  j={sp.N(j,12)}")

print()
for k in [1, sp.Rational(25, 4), 7]:
    # cubic: add root at infinity via homogenisation -> compute lambda among finite roots+inf
    R = 1 + k * t**3
    rs = [complex(r) for r in sp.Poly(R, t).all_roots()]
    e = sorted(rs, key=lambda z: __import__('math').atan2(z.imag, z.real))
    # lambda for cubic with one point at infinity: (e1-e2)/(e1-e3)
    lam = (e[0] - e[1]) / (e[0] - e[2])
    j = 256 * (1 - lam + lam**2)**3 / (lam**2 * (1 - lam)**2)
    print(f"cubic   1+{k} t^3 : lambda(approx)={sp.N(lam,12)}  j={sp.N(j,12)}")

print()
print("Jacobsthal j for the two curves: quartic j=1728 (lemniscatic), cubic j=0 (equianharmonic)")

# ---------- numeric check: boundary decompositions ----------
# P=4, k=9 (a=1,b=3):  L = (1/3) x sqrt(1+9x^4) + (2/3) I4
k = mpf(9); x = mpf('0.83')
L = quad(lambda u: sqrt(1 + k * u**4), [0, x])
I4 = quad(lambda u: 1 / sqrt(1 + k * u**4), [0, x])
print("\nP=4 decomposition residual:",
      L - (x * sqrt(1 + k * x**4) / 3 + mpf(2) / 3 * I4))

# P=3, k=25/4 (a=1,b=5/2): L = (2/5) x sqrt(1+k x^3) + (3/5) I3
k = mpf(25) / 4
L = quad(lambda u: sqrt(1 + k * u**3), [0, x])
I3 = quad(lambda u: 1 / sqrt(1 + k * u**3), [0, x])
print("P=3 decomposition residual:",
      L - (mpf(2) / 5 * x * sqrt(1 + k * x**3) + mpf(3) / 5 * I3))

# ---------- numeric check: modulus for quartic via Moebius fit ----------
# u(x)=int_0^x dt/sqrt(1+t^4).  Test  sn(C u, m) = (alpha x + beta)/(gamma x + delta).
def u4(xx):
    return quad(lambda u: 1 / sqrt(1 + u**4), [0, xx])

m = mpf(1) / 2
for Ctry in [sqrt(2), 1, 1 / sqrt(2), 2]:
    xs = [mpf('0.15'), mpf('0.45'), mpf('0.75'), mpf('0.95')]
    ys = [ellipfun('sn', Ctry * u4(xx), m) for xx in xs]
    # fit Moebius y = (a x + b)/(c x + d), normalise d=1
    A = []
    rhs = []
    for xx, yy in zip(xs, ys):
        A.append([xx, 1, -yy * xx])
        rhs.append(yy)
    import mpmath as mp
    sol = mp.lu_solve(A, rhs)
    a, b, c = sol
    vals = [(a * xx + b) / (c * xx + 1) for xx in xs]
    err = max(abs(v - yy) for v, yy in zip(vals, ys))
    print(f"  m=1/2, C={float(Ctry):.6f}: max Moebius-fit error = {mp.nstr(err,3)}")

# direct: check the amplitude relation for x->infinity normalisation
print("I4(1)=", mp.nstr(u4(mpf(1)), 20), " K(1/2)/sqrt2 =", mp.nstr(ellipk(mpf(1)/2)/sqrt(2), 20))
