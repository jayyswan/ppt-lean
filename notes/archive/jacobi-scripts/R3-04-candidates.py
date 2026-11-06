"""
R3 script 04: candidate composition formulas for the amplitude.
 (1) brief's reciprocal-modulus mixed E/F identity;
 (2) complete-integral Landen;
 (3) the master derivative-test identity on the lemniscate/single-curve examples;
 (4) test whether E_{c'}(am_c(u)) is constructible/elementary for natural c' relations;
 (5) test third-kind reducibility for special n via sympy.

Convention: parameter m=k^2.
"""
from mpmath import (mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, tan, asin,
                    atan, pi, findroot, quad, ellippi)
import mpmath as mpm

mp.dps = 40


def F(phi, k):
    return ellipf(phi, k ** 2)


def E(phi, k):
    return ellipe(phi, k ** 2)


def am(u, k):
    return findroot(lambda ph: F(ph, k) - u, u)


def sn(u, k):
    return ellipfun('sn', u, k ** 2)


def cn(u, k):
    return ellipfun('cn', u, k ** 2)


def dn(u, k):
    return ellipfun('dn', u, k ** 2)


print("== (1) reciprocal-modulus mixed E/F identity (brief), k>1 ==")
for k in [mpf('1.3'), mpf('1.7'), mpf('2.5')]:
    inv = 1 / k
    worry = mpf(0)
    for phi in [mpf('0.1'), mpf('0.25'), mpf('0.4'), mpf('0.55'), mpf('0.7')]:
        if k * sin(phi) >= 1:
            continue
        beta = asin(k * sin(phi))
        lhs = E(phi, k)
        rhs = k * E(beta, inv) - (k - 1 / k) * F(beta, inv)
        worry = max(worry, abs(lhs - rhs))
    print(f"k={k}: worst |E(phi,k) - [k E(beta,1/k) - (k-1/k) F(beta,1/k)]| = {mp.nstr(worry,4)}")

print()
print("== reciprocal F identity guess: F(phi,k) = ? F(beta,1/k) ==")
for k in [mpf('1.3'), mpf('1.7')]:
    inv = 1 / k
    phi = mpf('0.3')
    beta = asin(k * sin(phi))
    print(f"k={k}: F(phi,k)/F(beta,1/k)={mp.nstr(F(phi,k)/F(beta,inv),12)} "
          f" 1/k={mp.nstr(inv,12)} k={mp.nstr(k,12)}")

print()
print("== (2) complete-integral Landen K and E ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    l = (1 - sqrt(1 - k ** 2)) / (1 + sqrt(1 - k ** 2))
    Kk, Kl = ellipk(k ** 2), ellipk(l ** 2)
    Ek, El = E(pi / 2, k), E(pi / 2, l)
    print(f"k={mp.nstr(k,4)} l={mp.nstr(l,4)}: K(k)-(1+l)K(l)={mp.nstr(Kk-(1+l)*Kl,4)}, "
          f"E(k)-[(1+l)E(l)-l K(l)]={mp.nstr(Ek-((1+l)*El-l*Kl),4)}")

print()
print("== (4) is E_{c'}(am_c(u)) expressible as A*E_c(am_c)+B*u + algebraic(am_c)? ==")
# Build data over u; unknown A,B and algebraic poly in s=sin(am_c) (odd/even basis).
for c in [mpf('0.09'), mpf('0.49'), mpf('0.8649')]:
    k = sqrt(c)
    for cp in [1 - c, c ** 2, (1 - sqrt(1 - c * 1.0)), c / 2, 1.0]:
        kp = sqrt(cp) if cp >= 0 else None
        if kp is None or kp >= 1:
            continue
        us = [mpf(str(x)) for x in (0.2, 0.5, 0.9, 1.3, 1.8, 2.3)]
        # columns: E_c(am), u, s, s^2, s^3, s^4, s^5
        A = []
        y = []
        for u in us:
            phi = am(u, k)
            s = sin(phi)
            y.append(E(phi, kp))
            A.append([E(phi, k), u, s, s ** 2, s ** 3, s ** 4, s ** 5, mpf(1)])
        M = mpm.matrix(A)
        yv = mpm.matrix(y)
        sol = mpm.lu_solve(M.T * M, M.T * yv)
        resid = max(abs(y[i] - sum(sol[j] * A[i][j] for j in range(len(sol))))
                    for i in range(len(y)))
        print(f"c={mp.nstr(c,4)} c'={mp.nstr(cp,4)}: A={mp.nstr(sol[0],8)} B={mp.nstr(sol[1],8)} "
              f"polycoef={mp.nstr(sol[2],6)},{mp.nstr(sol[3],6)},{mp.nstr(sol[4],6)} "
              f"resid={mp.nstr(resid,4)}")
