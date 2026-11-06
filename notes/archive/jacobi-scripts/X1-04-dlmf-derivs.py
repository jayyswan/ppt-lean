# X1-04: calibration of the DLMF 19.4 derivative formulas used in the moving-modulus
# analysis, and a check that the E/F coefficients can be cancelled only by making the
# remaining right side algebraic in u (hence circular for dn).
#
# DLMF 19.4.6:  dE(phi,k)/dk = (E(phi,k) - F(phi,k))/k
# DLMF 19.4.5:  dF(phi,k)/dk = (E(phi,k) - k'^2 F(phi,k))/(k k'^2)
#                              - k sin(phi) cos(phi)/(k'^2 sqrt(1-k^2 sin^2 phi))
#
# In parameter m = k^2:
#   dE/dm = (E - F)/(2m)
#   dF/dm = (E - (1-m)F)/(2m(1-m)) - sin(phi)cos(phi)/(2(1-m)Delta)
# with Delta = sqrt(1-m sin^2 phi).

import mpmath as mp

mp.mp.dps = 30


def Einc(phi, m):
    return mp.quad(lambda t: mp.sqrt(1 - m * mp.sin(t) ** 2), [0, phi])


def out(*a):
    print(*a)


out("=== DLMF 19.4.6: dE/dk ===")
for m in [mp.mpf("0.09"), mp.mpf("0.5")]:
    k = mp.sqrt(m)
    for phi in [mp.mpf("0.4"), mp.mpf("1.2")]:
        num = mp.diff(lambda kk: Einc(phi, kk ** 2), k)
        E = Einc(phi, m)
        F = mp.ellipf(phi, m)
        pred = (E - F) / k
        out(f"  m={mp.nstr(m,4)} phi={mp.nstr(phi,4)}: dE/dk num={mp.nstr(num,18)} "
            f"pred={mp.nstr(pred,18)} resid={mp.nstr(abs(num-pred),4)}")

out("")
out("=== DLMF 19.4.5: dF/dk ===")
for m in [mp.mpf("0.09"), mp.mpf("0.5")]:
    k = mp.sqrt(m)
    kp2 = 1 - m
    for phi in [mp.mpf("0.4"), mp.mpf("1.2")]:
        num = mp.diff(lambda kk: mp.ellipf(phi, kk ** 2), k)
        E = Einc(phi, m)
        F = mp.ellipf(phi, m)
        D = mp.sqrt(1 - m * mp.sin(phi) ** 2)
        pred = (E - kp2 * F) / (k * kp2) - k * mp.sin(phi) * mp.cos(phi) / (kp2 * D)
        out(f"  m={mp.nstr(m,4)} phi={mp.nstr(phi,4)}: dF/dk num={mp.nstr(num,18)} "
            f"pred={mp.nstr(pred,18)} resid={mp.nstr(abs(num-pred),4)}")

out("")
out("=== coefficient check for am = a1 E(phi,m) + a2 F(phi,m) + a3 (all functions of u) ===")
out("d/dn: coefficient of E is a1' + (m'/(2m)) a1 + (m'/(2m(1-m))) a2")
out("      coefficient of F is a2' - (m'/(2m)) a1 - (m'/(2m)) a2")
out("Setting both to 0 makes the right side algebraic in (phi,m,a_i), so")
out("dn_c(u) = algebraic(phi(u),m(u),a_i(u),phi'(u),m'(u)):")
out("possible only if phi or m already depends on am_c (circular).")
