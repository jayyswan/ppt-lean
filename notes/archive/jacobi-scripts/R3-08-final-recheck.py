"""
R3 script 08: final INDEPENDENT arithmetic re-check. Fresh code, no imports from the other
R3 scripts; recomputes the load-bearing numbers and prints full residuals.

Run: C:\\Users\\jason\\AppData\\Local\\Programs\\Python\\Python312\\python.exe R3-08-final-recheck.py
"""
from mpmath import mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, asin, tan, \
    atan2, pi, quad, findroot
import numpy as np

mp.dps = 45
K = [mpf('0.3'), mpf('0.7'), mpf('0.93')]
U = [mpf('0.2'), mpf('0.85'), mpf('1.6'), mpf('3.1'), mpf('5.4')]

sn = lambda u, k: ellipfun('sn', u, k ** 2)
cn = lambda u, k: ellipfun('cn', u, k ** 2)
dn = lambda u, k: ellipfun('dn', u, k ** 2)
F = lambda p, k: ellipf(p, k ** 2)
E = lambda p, k: ellipe(p, k ** 2)


def am(u, k):
    return findroot(lambda p: F(p, k) - u, u, tol=mpf('1e-43'))


print("[1] Landen sn identity  sn(z,k)=(1+l)sn(v,l)/(1+l sn^2),  z=(1+l)v, l=(1-k')/(1+k')")
w = mpf(0)
for k in K:
    l = (1 - sqrt(1 - k ** 2)) / (1 + sqrt(1 - k ** 2))
    assert abs(k - 2 * sqrt(l) / (1 + l)) < mpf('1e-42')
    for u in U:
        v = u / (1 + l)
        s = sn(v, l)
        w = max(w, abs(sn(u, k) - (1 + l) * s / (1 + l * s ** 2)),
                abs(cn(u, k) - cn(v, l) * dn(v, l) / (1 + l * s ** 2)),
                abs(dn(u, k) - (1 - l * s ** 2) / (1 + l * s ** 2)))
print("    worst residual:", mp.nstr(w, 5))

print("[2] reciprocal modulus: E(phi,k)=k E(beta,1/k)-(k-1/k) F(beta,1/k), k sin phi=sin beta")
w = mpf(0)
for k in [mpf('1.3'), mpf('1.7'), mpf('2.5')]:
    inv = 1 / k
    for phi in [mpf('0.1'), mpf('0.25'), mpf('0.4'), mpf('0.55'), mpf('0.7')]:
        beta = asin(k * sin(phi))
        w = max(w, abs(E(phi, k) - (k * E(beta, inv) - (k - inv) * F(beta, inv))))
print("    worst residual:", mp.nstr(w, 5))

print("[3] duplication  sn(2u)=2 sn cn dn/(1-c sn^4)")
w = mpf(0)
for k in K:
    c = k ** 2
    for u in U:
        s = sn(u, k)
        w = max(w, abs(sn(2 * u, k) - 2 * s * cn(u, k) * dn(u, k) / (1 - c * s ** 4)))
print("    worst residual:", mp.nstr(w, 5))

print("[4] epsilon identity  E_c(am_c(u)) = int_0^u dn_c(t)^2 dt")
w = mpf(0)
for k in K:
    for u in U:
        w = max(w, abs(E(am(u, k), k) - quad(lambda t: dn(t, k) ** 2, [0, u])))
print("    worst residual:", mp.nstr(w, 5))

print("[5] mixed E/F off-grid: no identity E_{c'}(am_c)=A E_c(am_c)+B u+poly(s), c'!=c")
c = mpf('0.49')
fg = [mpf(str(0.15 + 0.11 * i)) for i in range(14)]
tg = [mpf(str(0.17 + 0.13 * i)) for i in range(12)]


def offgrid(cp, sdeg):
    k = sqrt(c)
    def row(u):
        s = sin(am(u, k)); b = sqrt((1 - s ** 2) * (1 - c * s ** 2))
        return [1 - c * s ** 2, mpf(1)] + [s ** j * b for j in range(sdeg + 1)], \
            sqrt((1 - cp * s ** 2) * (1 - c * s ** 2))
    R = [row(u) for u in fg]
    M = mp.matrix([r[0] for r in R]); y = mp.matrix([r[1] for r in R])
    sol = mp.lu_solve(M.T * M, M.T * y)
    return max(abs(r[1] - sum(sol[j] * r[0][j] for j in range(len(sol)))) for r in [row(u) for u in tg])


for cp, tag in [(c, "c'=c   (must be 0)"), (1 - c, "c'=1-c"), (c / 2, "c'=c/2")]:
    print(f"    {tag}: off-grid residual (sdeg=8) = {mp.nstr(offgrid(cp, 8), 5)}")

print("DONE")
