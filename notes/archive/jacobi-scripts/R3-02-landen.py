"""
R3 script 02: identify the Landen/Gauss (ascending and descending) transformations for the
amplitude, sn/cn/dn, and the incomplete E (Jacobi epsilon). Then test whether a change of
modulus can convert an E-integral into an F-integral (the mixed E/F loophole).

Run with the Python 3.12 at C:\\Users\\<user>\\AppData\\Local\\Programs\\Python\\Python312\\python.exe
"""
from mpmath import (mp, mpf, ellipfun, ellipf, ellipe, ellipk, sqrt, sin, cos, tan, atan,
                    quad, pi, findroot, mpc)

mp.dps = 40


def F(phi, k):
    return ellipf(phi, k ** 2)


def E(phi, k):
    return ellipe(phi, k ** 2)


def am(u, k):
    f = lambda ph: F(ph, k) - u
    return findroot(f, u)


def sn(u, k):
    return ellipfun('sn', u, k ** 2)


def cn(u, k):
    return ellipfun('cn', u, k ** 2)


def dn(u, k):
    return ellipfun('dn', u, k ** 2)


def epsilon(u, k):
    # Jacobi epsilon: int_0^u dn(s)^2 ds = E(am(u,k),k)
    return E(am(u, k), k)


MODS = [mpf('0.3'), mpf('0.7'), mpf('0.93')]
ARGS = [mpf('0.2'), mpf('0.85'), mpf('1.6'), mpf('3.1'), mpf('5.4')]


def landen_l(k):
    kp = sqrt(1 - k ** 2)
    return (1 - kp) / (1 + kp)


print("== identify Landen: k -> l=(1-k')/(1+k'); check u vs (1+l)v ==")
for k in MODS:
    l = landen_l(k)
    print(f"k={mp.nstr(k,6)}  l={mp.nstr(l,6)}  (1+l)={mp.nstr(1+l,6)}")
    for u in ARGS[:2]:
        a = am(u, k)
        for sc, lab in [(u / (1 + l), "v=u/(1+l)"), (u * (1 + l), "v=u(1+l)")]:
            v = sc
            s1 = sn(v, l)
            # three candidate amplitude relations
            cands = {
                "sn_landen": (1 + l) * s1 / (1 + l * s1 ** 2),
                "sin(2phi1-phi)=k sinphi": sin(2 * am(v, l) - a) - k * sin(a),
                "tan(phi1-phi)=kp tanphi": tan(am(v, l) - a) - sqrt(1 - k ** 2) * tan(a),
            }
            print("   ", lab, {nm: mp.nstr(val, 4) for nm, val in cands.items()})

print()
print("== amplitude relation candidates (descending: am(u,k) from am(v,l), v=u/(1+l)) ==")
for k in MODS:
    l = landen_l(k)
    kp = sqrt(1 - k ** 2)
    worst = {}
    for u in ARGS:
        v = u / (1 + l)
        phi1 = am(v, l)
        phi = am(u, k)
        tests = {
            "sin(2phi1-phi)-k sinphi": sin(2 * phi1 - phi) - k * sin(phi),
            "tan(phi1-phi)-kp tanphi": tan(phi1 - phi) - kp * tan(phi),
            "sinphi-(1+l)sn/(1+l sn^2)": sin(phi) - (1 + l) * sn(v, l) / (1 + l * sn(v, l) ** 2),
        }
        for nm, val in tests.items():
            worst[nm] = max(worst.get(nm, mpf(0)), abs(val))
    print(f"k={mp.nstr(k,4)} l={mp.nstr(l,4)}")
    for nm, val in worst.items():
        print(f"    {nm}  worst={mp.nstr(val,4)}")
