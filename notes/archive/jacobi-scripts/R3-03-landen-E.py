"""
R3 script 03: verify the Landen transformation of sn/cn/dn and am; find the transformation
of the incomplete E (Jacobi epsilon); test whether an E-integral at one modulus can be
turned into an F-integral at another (the mixed E/F loophole); verify Legendre's relation
and the real/imaginary modulus transformations.

Convention: parameter m=k^2.
"""
from mpmath import (mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, tan, atan,
                    quad, pi, findroot, mpc, ellippi)

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


def landen_l(k):
    return (1 - sqrt(1 - k ** 2)) / (1 + sqrt(1 - k ** 2))


MODS = [mpf('0.3'), mpf('0.7'), mpf('0.93')]
ARGS = [mpf('0.2'), mpf('0.85'), mpf('1.6'), mpf('3.1'), mpf('5.4')]

print("== Landen sn/cn/dn relations, u=(1+l)v, l=(1-k')/(1+k'), k=2 sqrt(l)/(1+l) ==")
for k in MODS:
    l = landen_l(k)
    worst = {'sn': mpf(0), 'cn': mpf(0), 'dn': mpf(0), 'k_rescale': mpf(0),
             'sin_am': mpf(0)}
    for u in ARGS:
        v = u / (1 + l)
        s, c, d = sn(v, l), cn(v, l), dn(v, l)
        den = 1 + l * s ** 2
        worst['sn'] = max(worst['sn'], abs(sn(u, k) - (1 + l) * s / den))
        worst['cn'] = max(worst['cn'], abs(cn(u, k) - c * d / den))
        worst['dn'] = max(worst['dn'], abs(dn(u, k) - (1 - l * s ** 2) / den))
        worst['k_rescale'] = max(worst['k_rescale'], abs(k - 2 * sqrt(l) / (1 + l)))
        worst['sin_am'] = max(worst['sin_am'], abs(sin(am(u, k)) - (1 + l) * s / den))
    print(f"k={mp.nstr(k,4)} l={mp.nstr(l,4)} worst=" +
          ", ".join(f"{nm}:{mp.nstr(val,3)}" for nm, val in worst.items()))

print()
print("== incomplete E under Landen: fit E(phi,k) as a*E(phi1,l)+b*F(phi1,l)+const ==")
for k in MODS:
    l = landen_l(k)
    # data points
    rows = []
    for u in ARGS:
        phi = am(u, k)
        phi1 = am(u / (1 + l), l)
        rows.append((E(phi, k), E(phi1, l), F(phi1, l)))
    # solve least squares exactly for a,b and check residual (assume const=0 since phi=0)
    import mpmath
    A = mp.matrix([[r[1], r[2]] for r in rows])
    y = mp.matrix([r[0] for r in rows])
    sol = mp.lu_solve(A.T * A, A.T * y)
    a, b = sol[0], sol[1]
    resid = max(abs(r[0] - a * r[1] - b * r[2]) for r in rows)
    print(f"k={mp.nstr(k,4)} l={mp.nstr(l,4)}: a={mp.nstr(a,10)} b={mp.nstr(b,10)} "
          f"resid={mp.nstr(resid,4)}")
    print(f"     (1+l)={mp.nstr(1+l,10)}  -l={mp.nstr(-l,10)}  b/(a-?)")

print()
print("== complete integrals: E(k) vs Landen; Legendre relation ==")
for k in MODS:
    l = landen_l(k)
    kp = sqrt(1 - k ** 2)
    leg = E(pi / 2, k) * ellipk((1 - k ** 2)) + E(pi / 2, kp) * ellipk(k ** 2) \
        - ellipk(k ** 2) * ellipk(1 - k ** 2) - pi / 2
    print(f"k={mp.nstr(k,4)}: E(k)={mp.nstr(E(pi/2,k),8)} l={mp.nstr(l,6)} "
          f"E(l)={mp.nstr(E(pi/2,l),8)} ratio E(l)/E(k)={mp.nstr(E(pi/2,l)/E(pi/2,k),8)} "
          f"Legendre residual={mp.nstr(leg,4)}")

print()
print("== reciprocal/imaginary modulus: F(phi,k) for k>1? test k->1/k real transformation ==")
# real transformation (DLMF 19.7.5): for 0<k<1, with k sin(phi)=sin(psi)? test numerically later
for k in [mpf('0.3'), mpf('0.7')]:
    print(f"k={k}: skipped detailed; placeholder")
