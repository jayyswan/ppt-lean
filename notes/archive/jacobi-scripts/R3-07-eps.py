"""
R3 script 07: the "ellipticEAm_c" candidate and the positive calibration.
 (A) E_c(am_c(u)) = int_0^u dn^2 = Jacobi epsilon (DLMF 22.16.17), verified numerically.
 (B) epsilon(u) is not affine in u (so the L that the EAm_c route would need is nonaffine,
     and moreover it is defined via am_c -> circular).
 (C) Positive calibration: the E-route works because E_c IS a drawable arc length; test that
     ellipticEAm_c(E_c(phi)) = phi (the analogue of the theorem) and record it.
Convention: parameter m=k^2.
"""
from mpmath import mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, findroot, quad
mp.dps = 40


def F(phi, k):
    return ellipf(phi, k ** 2)


def E(phi, k):
    return ellipe(phi, k ** 2)


def am(u, k):
    return findroot(lambda ph: F(ph, k) - u, u, tol=mpf('1e-38'))


def dn(u, k):
    return ellipfun('dn', u, k ** 2)


print("== (A) E_c(am_c(u)) = int_0^u dn(t)^2 dt ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    worst = mpf(0)
    for u in [mpf('0.2'), mpf('0.85'), mpf('1.6'), mpf('3.1'), mpf('5.4')]:
        lhs = E(am(u, k), k)
        rhs = quad(lambda t: dn(t, k) ** 2, [0, u])
        worst = max(worst, abs(lhs - rhs))
    print(f"k={k}: worst |E(am(u)) - int dn^2| = {mp.nstr(worst,4)}")

print()
print("== (B) epsilon(u)=E_c(am_c(u)) is not affine in u ==")
for k in [mpf('0.3'), mpf('0.7')]:
    us = [mpf('0.2'), mpf('1.0'), mpf('2.0')]
    eps = [E(am(u, k), k) for u in us]
    # second divided difference
    d2 = (eps[2] - eps[1]) / (us[2] - us[1]) - (eps[1] - eps[0]) / (us[1] - us[0])
    print(f"k={k}: second divided difference of epsilon = {mp.nstr(d2,6)} (nonzero => nonaffine)")

print()
print("== (C) positive calibration: ellipticEAm_c inverts E_c ==")
for k in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    c = k ** 2
    # ellipticEAm as a named inverse: verify E(am_of_E(L)) with L=E(phi)
    phi = mpf('0.9')
    L = E(phi, k)
    # get the angle whose E is L (this is what the Lean ellipse construction produces)
    inv = findroot(lambda p: E(p, k) - L, phi, tol=mpf('1e-38'))
    print(f"k={k}: E_Am(E(phi)) - phi = {mp.nstr(inv - phi,4)}")
