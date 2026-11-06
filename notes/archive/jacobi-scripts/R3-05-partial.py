"""
R3 script 05 (v3): partial facts about which u have constructible amplitude.
 (a) duplication formula for sn;
 (b) halving: given S=sn(2u), x=sn(u) is a root of a quartic in y=x^2 -> constructible;
 (c) addition closure via sn/cn addition (F4);
 (d) u = r*K for dyadic r via repeated halving.

Convention: parameter m=k^2.
"""
from mpmath import (mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, asin, acos,
                    atan2, pi, findroot)
import numpy as np

mp.dps = 50


def F(phi, k):
    return ellipf(phi, k ** 2)


def am(u, k):
    return findroot(lambda ph: F(ph, k) - u, u, tol=mpf('1e-48'))


def sn(u, k):
    return ellipfun('sn', u, k ** 2)


def cn(u, k):
    return ellipfun('cn', u, k ** 2)


def dn(u, k):
    return ellipfun('dn', u, k ** 2)


def halve_sn_roots(S, c):
    """Positive real y=x^2 roots of S^2(1-c y^2)^2 = 4y(1-y)(1-cy), refined to full dps."""
    coeffs = [S ** 2, mpf(-4), 4 * (1 + c) - 2 * c * S ** 2, -4 * c, c ** 2 * S ** 2]

    def poly(yy):
        acc = mpf(0)
        for co in reversed(coeffs):
            acc = acc * yy + co
        return acc

    r0 = np.roots([float(x) for x in coeffs[::-1]])
    out = []
    for r in r0:
        if abs(r.imag) < 1e-6 and r.real > 0:
            try:
                out.append(mp.findroot(poly, mpf(r.real)))
            except Exception:
                pass
    return out


print("== (a) duplication: sn(2u) = 2 sn cn dn / (1 - c sn^4) ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    worst = mpf(0)
    for u in [mpf('0.2'), mpf('0.85'), mpf('1.6'), mpf('3.1'), mpf('5.4')]:
        s = sn(u, k)
        rhs = 2 * s * cn(u, k) * dn(u, k) / (1 - c * s ** 4)
        worst = max(worst, abs(sn(2 * u, k) - rhs))
    print(f"k={k}: worst={mp.nstr(worst,4)}")

print()
print("== (b) halving recovers sn(u) from S=sn(2u) ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    for u in [mpf('0.37'), mpf('1.23')]:
        S = sn(2 * u, k)
        ys = halve_sn_roots(S, c)
        xroots = [sqrt(rr) for rr in ys]
        got = sn(u, k)
        ok = any(abs(xx - got) < mpf('1e-30') for xx in xroots)
        print(f"k={k} u={u}: #positive y-roots={len(ys)} sn(u) recovered={ok} sn={mp.nstr(got,8)}")

print()
print("== (c) addition: am(u+v) from am(u),am(v) via sn/cn addition ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    worst = mpf(0)
    for u, v in [(mpf('0.3'), mpf('0.7')), (mpf('1.1'), mpf('-0.4')),
                 (mpf('2.2'), mpf('3.3')), (mpf('-1.9'), mpf('0.85'))]:
        au, av = am(u, k), am(v, k)
        su, cu, du = sin(au), cos(au), dn(u, k)
        sv, cv, dv = sin(av), cos(av), dn(v, k)
        den = 1 - c * su ** 2 * sv ** 2
        cnum = (cu * cv - su * sv * du * dv) / den
        snum = (su * cv * dv + sv * cu * du) / den
        cand = atan2(snum, cnum)
        target = am(u + v, k)
        r = (cand - target) / (2 * pi)
        d = abs(r - mp.nint(r)) * 2 * pi
        worst = max(worst, d)
    print(f"k={k}: worst |am(u+v) reconstructed - am(u+v)| (mod 2pi) = {mp.nstr(worst,4)}")

print()
print("== (d) dyadic: seed am(K)=pi/2; current angle phi=am(2u), S=sin(phi); halve ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    K = ellipk(c)
    phi = pi / 2
    worst = mpf(0)
    for n in range(1, 7):
        S = sin(phi)                       # sn(2u) for u with am(2u)=phi
        ys = halve_sn_roots(S, c)
        xr = [sqrt(rr) for rr in ys if 0 < rr <= 1]
        if not xr:
            break
        xbest = min(xr, key=lambda xx: abs(xx - sin(phi / 2)))
        phi = asin(xbest)
        target = am(K / 2 ** n, k)
        worst = max(worst, abs(phi - target))
    print(f"k={k}: worst over n=1..8 of |am(K/2^n) - halving| = {mp.nstr(worst,4)}")
