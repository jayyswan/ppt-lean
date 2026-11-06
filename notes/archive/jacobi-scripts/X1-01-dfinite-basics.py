# X1-01: D-finiteness basics for the "measured length" route.
#
# Checks:
#  (A) The COMPLETE Legendre integrals K(m), E(m) are D-finite: verify their known
#      second-order linear ODEs with polynomial coefficients to high precision.
#  (B) The INCOMPLETE integrals E(phi,m), F(phi,m), as functions of phi, are NOT D-finite:
#      they have infinitely many complex branch points. Locate the branch points
#      (sin^2 phi = 1/m) and measure the local exponent.
#  (C) am(u,m) is NOT D-finite: am' = dn has simple poles on the infinite lattice
#      u = iK' + 2Z K + 2Z iK'; find them numerically.
#  (D) Calibration: ellipse arc length = E(phi,c), sine-curve arc length = moving-modulus E.
#
# Convention: mpmath parameter m = c = k^2.  Run under 30 s.

import mpmath as mp

mp.mp.dps = 40


def out(*a):
    print(*a)


out("=== (A) complete K(m), E(m) satisfy second-order linear ODEs ===")
for m in [mp.mpf("0.09"), mp.mpf("0.3"), mp.mpf("0.7"), mp.mpf("0.93")]:
    K = lambda x: mp.ellipk(x)
    E = lambda x: mp.ellipe(x)
    K0, K1, K2 = K(m), mp.diff(K, m, 1), mp.diff(K, m, 2)
    E0, E1, E2 = E(m), mp.diff(E, m, 1), mp.diff(E, m, 2)
    rK = m * (1 - m) * K2 + (1 - 2 * m) * K1 - K0 / 4
    rE = m * (1 - m) * E2 + (1 - m) * E1 + E0 / 4
    out(f"  m={mp.nstr(m,5)}: |K-ODE resid|={mp.nstr(abs(rK),5)}  "
        f"|E-ODE resid|={mp.nstr(abs(rE),5)}")

out("")
out("=== (B) incomplete E(phi,m), F(phi,m) have infinitely many branch points ===")
out("    branch point at sin^2 phi = 1/m; check local exponent of E and F")
for mm in [mp.mpf("0.09"), mp.mpf("0.5")]:
    one_over_sqrt = 1 / mp.sqrt(mm)
    phistar = mp.asin(one_over_sqrt)            # complex angle
    out(f"  m={mp.nstr(mm,4)}  phistar={mp.nstr(phistar,20)}")
    # E(phi,m) = int_0^phi sqrt(1-m sin^2 t) dt  (complex path)
    Eint = lambda z: mp.quad(lambda t: mp.sqrt(1 - mm * mp.sin(t) ** 2), [0, z])
    Fint = lambda z: mp.quad(lambda t: 1 / mp.sqrt(1 - mm * mp.sin(t) ** 2), [0, z])
    base = phistar + mp.mpf("0.37")             # a nearby regular point
    Eref = Eint(base)
    Fref = Fint(base)
    # move toward phistar with step h; exponent from ratio of increments
    prevE = prevF = None
    for h in [mp.mpf("1e-4"), mp.mpf("1e-5"), mp.mpf("1e-6")]:
        zE = Eint(phistar + h) - Eref
        zF = Fint(phistar + h) - Fref
        zE0 = Eint(base) - Eref
        zF0 = Fint(base) - Fref
        # local: (zE(phistar+h)-E(phistar)) ~ C h^alpha ; estimate alpha via log ratio
        # E(phistar) itself: use h=1e-4 and 1e-5:
        out(f"    h={mp.nstr(h,3)}  E(phistar+h)-Eref={mp.nstr(zE,10)}  "
            f"F(...)={mp.nstr(zF,10)}")
    # exponent estimate for E: (E(p+h)-E(p)) / (E(p+h/4)-E(p)) -> 4^alpha
    h1, h4 = mp.mpf("1e-5"), mp.mpf("1e-5") / 4
    dE1 = Eint(phistar + h1) - Eint(phistar + h4)
    dE2 = Eint(phistar + h4) - Eint(phistar + h4 / 4)
    dF1 = Fint(phistar + h1) - Fint(phistar + h4)
    dF2 = Fint(phistar + h4) - Fint(phistar + h4 / 4)
    alphaE = mp.log(dE1 / dE2) / mp.log(4)
    alphaF = mp.log(dF1 / dF2) / mp.log(4)
    out(f"    local exponent E ~ h^alpha: alpha={mp.nstr(alphaE,8)} (expect 1.5)")
    out(f"    local exponent F ~ h^alpha: alpha={mp.nstr(alphaF,8)} (expect 0.5)")
    out(f"    branch points repeat every pi: next={mp.nstr(phistar+mp.pi,20)}")

out("")
out("=== (C) am(u) is not D-finite: dn = am' has simple poles on a lattice ===")
for mm in [mp.mpf("0.09"), mp.mpf("0.7")]:
    Kp = mp.ellipk(1 - mm)                       # iK' imaginary period/2
    out(f"  m={mp.nstr(mm,4)}  iK' = {mp.nstr(1j*Kp,20)}")
    for n in range(0, 3):
        # poles of dn at (2n+1) iK' (on the imaginary axis) -- also 2K+ that
        target = (2 * n + 1) * 1j * Kp
        # solve 1/dn = 0
        try:
            pole = mp.findroot(lambda u: 1 / mp.ellipfun('dn', u, mm), target + 0.01)
            out(f"    pole dn at u={mp.nstr(pole,20)}  resid(dn)~ "
                f"{mp.nstr(mp.limit(lambda u: (u-pole)*mp.ellipfun('dn',u,mm), pole),12)}")
        except Exception as e:
            out(f"    pole search at {mp.nstr(target,12)} failed: {e}")
    # second family: 2K + iK'
    K = mp.ellipk(mm)
    target = 2 * K + 1j * Kp
    try:
        pole = mp.findroot(lambda u: 1 / mp.ellipfun('dn', u, mm), target + 0.01)
        out(f"    pole dn at 2K+iK' -> {mp.nstr(pole,20)} "
            f"(2K+iK'={mp.nstr(target,20)})")
    except Exception as e:
        out(f"    second-family pole search failed: {e}")

out("")
out("=== (D) calibration: arc lengths ===")
# ellipse x=a cos t, y=b sin t, a^2=1-c, b=1: speed = sqrt((1-c) sin^2 t + cos^2 t)
# = sqrt(1 - c sin^2 t) = E'.  Arc [0,phi] = E(phi,c).
c = mp.mpf("0.37")
a = mp.sqrt(1 - c)
phi = mp.mpf("1.1")
speed = lambda t: mp.sqrt(a ** 2 * mp.sin(t) ** 2 + mp.cos(t) ** 2)
arc = mp.quad(speed, [0, phi])
Einc = mp.quad(lambda t: mp.sqrt(1 - c * mp.sin(t) ** 2), [0, phi])
out(f"  ellipse arc vs E(phi,c): residual = {mp.nstr(abs(arc - Einc),5)}")

# sine curve y=A sin(Bx), x in [0,X]: L = int_0^X sqrt(1+A^2 B^2 cos^2(Bx)) dx
#   = (sqrt(1+A^2 B^2)/B) * E(BX, m)  with m = A^2 B^2/(1+A^2 B^2)
A = mp.mpf("0.8")
B = mp.mpf("1.3")
X = mp.mpf("0.9")
Lsine = mp.quad(lambda x: mp.sqrt(1 + A ** 2 * B ** 2 * mp.cos(B * x) ** 2), [0, X])
mpar = A ** 2 * B ** 2 / (1 + A ** 2 * B ** 2)
Eform = (mp.sqrt(1 + A ** 2 * B ** 2) / B) * mp.quad(
    lambda t: mp.sqrt(1 - mpar * mp.sin(t) ** 2), [0, B * X])
out(f"  sine arc vs moving-modulus E: residual = {mp.nstr(abs(Lsine - Eform),5)}")
out(f"  modulus m(A,B) = {mp.nstr(mpar,20)}")
