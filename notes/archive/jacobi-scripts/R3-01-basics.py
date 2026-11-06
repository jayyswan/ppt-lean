"""
R3 script 01: mpmath conventions for the Jacobi/elliptic functions, and sanity checks
of the facts the R3 brief relies on.

Convention: mpmath.ellipfun(kind, u, m) takes the PARAMETER m = k^2 (also accepts k=).
mpmath.ellipf(phi, m), ellipe(phi, m) are incomplete F and E; ellipk(m), ellipe(m)
one-arg are complete K, E.

Run: C:\\Users\\<user>\\AppData\\Local\\Programs\\Python\\Python312\\python.exe R3-01-basics.py
"""
from mpmath import mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, quad, pi, findroot

mp.dps = 40


def F(phi, k):
    return ellipf(phi, k ** 2)


def E(phi, k):
    return ellipe(phi, k ** 2)


def am(u, k):
    # invert F(.,k) by Newton; F is strictly increasing
    f = lambda ph: F(ph, k) - u
    # good initial guess: k=0 => phi=u
    guess = u if abs(u) < 1 else mp.sign(u)
    try:
        return findroot(f, [guess - mpf(2), guess + mpf(2), guess])
    except Exception:
        return findroot(f, u)


def sn(u, k):
    return ellipfun('sn', u, k ** 2)


def cn(u, k):
    return ellipfun('cn', u, k ** 2)


def dn(u, k):
    return ellipfun('dn', u, k ** 2)


print("== convention checks ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    for u in [mpf('0.2'), mpf('1.0'), mpf('2.3'), mpf('-1.7'), mpf('5.1')]:
        a = am(u, k)
        r1 = F(a, k) - u
        r2 = sn(u, k) - sin(a)
        r3 = dn(u, k) - sqrt(1 - k ** 2 * sin(a) ** 2)
        print("k=%s u=%s  F(am)-u=%s  sn-sinam=%s  dn-D=%s"
              % (k, u, mp.nstr(r1, 5), mp.nstr(r2, 5), mp.nstr(r3, 5)))

print()
print("== (F4) cn addition theorem: cn(u+v) = (cu cv - su sv du dv)/(1 - c su^2 sv^2) ==")
for k in [mpf('0.3'), mpf('-2.5'), mpf('0.93')]:
    c = k ** 2
    worst = mpf(0)
    for u, v in [(mpf('0.3'), mpf('0.7')), (mpf('1.1'), mpf('-0.4')),
                 (mpf('2.2'), mpf('3.3')), (mpf('-1.9'), mpf('0.85')), (mpf('4.4'), mpf('0.15'))]:
        lhs = cn(u + v, k)
        rhs = (cn(u, k) * cn(v, k) - sn(u, k) * sn(v, k) * dn(u, k) * dn(v, k)) / \
              (1 - c * sn(u, k) ** 2 * sn(v, k) ** 2)
        worst = max(worst, abs(lhs - rhs))
    print(f"k={k}: worst residual = {mp.nstr(worst, 5)}")
