# X1-02: what `offset` does to a measured length.
#
# For a regular plane curve gamma with speed v, unit tangent t, unit normal n and signed
# curvature kappa, the offset gamma_d = gamma + d*n satisfies
#     gamma_d' = v (1 - d kappa) t,
# so speed(gamma_d) = v |1 - d kappa|.  In particular, per unit of arc length,
# the offset adds -d * (turning angle).  On a closed convex curve the total turning is
# 2*pi, giving the classical parallel-curve perimeter P -+ 2 pi d (Steiner).
#
# Consequence: for an algebraic base curve kappa is algebraic, so v(1-d kappa) is again an
# algebraic differential. `offset` does not manufacture a first-kind (pole-free) differential.
# Verified numerically below.

import mpmath as mp

mp.mp.dps = 40


def out(*a):
    print(*a)


out("=== speed factor |1 - d kappa| on a circle and an ellipse ===")

# --- circle radius r: gamma(t) = (r cos t, r sin t) ---
r = mp.mpf("1.7")
d = mp.mpf("0.6")


def circle(t):
    return (r * mp.cos(t), r * mp.sin(t))


def circle_d(t):
    return (-r * mp.sin(t), r * mp.cos(t))


def offp(g, gp, t, dd):
    v = mp.sqrt(gp(t)[0] ** 2 + gp(t)[1] ** 2)
    # unit normal = (-y', x')/v
    nx, ny = -gp(t)[1] / v, gp(t)[0] / v
    return (g(t)[0] + dd * nx, g(t)[1] + dd * ny)


for t in [mp.mpf("0.3"), mp.mpf("1.1"), mp.mpf("2.4")]:
    # numeric derivative of the offset curve
    spd = mp.sqrt(sum((mp.diff(lambda s: offp(circle, circle_d, s, d)[i], t)) ** 2
                      for i in range(2)))
    v = mp.sqrt(circle_d(t)[0] ** 2 + circle_d(t)[1] ** 2)
    kappa = mp.mpf(1) / r
    pred = v * abs(1 - d * kappa)
    out(f"  circle  t={mp.nstr(t,4)}: numeric={mp.nstr(spd,20)} pred={mp.nstr(pred,20)} "
        f"resid={mp.nstr(abs(spd-pred),5)}")

# --- ellipse a=sqrt(1-c), b=1  (so speed = Delta_c(t) = E integrand) ---
c = mp.mpf("0.37")
a = mp.sqrt(1 - c)
d2 = mp.mpf("0.35")


def ell(t):
    return (a * mp.cos(t), mp.sin(t))


def ell_d(t):
    return (-a * mp.sin(t), mp.cos(t))


def ell_dd(t):
    return (-a * mp.cos(t), -mp.sin(t))


for t in [mp.mpf("0.4"), mp.mpf("1.3"), mp.mpf("2.2")]:
    x, y = ell(t)
    x1, y1 = ell_d(t)
    x2, y2 = ell_dd(t)
    v = mp.sqrt(x1 ** 2 + y1 ** 2)
    kappa = (x1 * y2 - y1 * x2) / v ** 3
    spd = mp.sqrt(sum((mp.diff(lambda s: offp(ell, ell_d, s, d2)[i], t)) ** 2
                      for i in range(2)))
    pred = v * abs(1 - d2 * kappa)
    out(f"  ellipse t={mp.nstr(t,4)}: numeric={mp.nstr(spd,20)} pred={mp.nstr(pred,20)} "
        f"resid={mp.nstr(abs(spd-pred),5)}")

out("")
out("=== offset arc length = base arc length - d * (turning angle) ===")
# arcLengthOf offset over [0,phi]:
#   int_0^phi v|1-d kappa| dt = E_c(phi) - d*(theta(phi)-theta(0))   (d small, no cusp)
for c in [mp.mpf("0.37"), mp.mpf("0.7")]:
    a = mp.sqrt(1 - c)
    for d3 in [mp.mpf("0.2"), mp.mpf("-0.15")]:
        phi = mp.mpf("1.4")
        def off_arc():
            return mp.quad(lambda t: mp.sqrt(
                (mp.diff(lambda s: offp(ell, ell_d, s, d3)[0], t)) ** 2 +
                (mp.diff(lambda s: offp(ell, ell_d, s, d3)[1], t)) ** 2), [0, phi])
        offL = off_arc()
        Ephi = mp.quad(lambda t: mp.sqrt(1 - c * mp.sin(t) ** 2), [0, phi])
        # turning angle of ellipse: theta = atan2(y', x')
        th = lambda t: mp.atan2(mp.cos(t), -a * mp.sin(t))
        turn = th(phi) - th(mp.mpf("0"))
        pred = Ephi - d3 * turn
        out(f"  c={mp.nstr(c,3)} d={mp.nstr(d3,3)}: offset_arc={mp.nstr(offL,20)} "
            f"E-d*turn={mp.nstr(pred,20)} resid={mp.nstr(abs(offL-pred),5)}")

out("")
out("=== closed parallel-curve perimeter (Steiner) ===")
for c in [mp.mpf("0.37"), mp.mpf("0.7")]:
    a = mp.sqrt(1 - c)
    for d3 in [mp.mpf("0.1"), mp.mpf("-0.2")]:
        P = 4 * mp.ellipe(c)                    # full ellipse perimeter, semi-axes a,1
        # offset full loop: measure numerically via 1-d kappa formula
        # signed: because the curve is convex, speed = v(1-d kappa) for either sign of d
        # (kappa>0), so perimeter_off = P - d*2*pi.
        offP = P - d3 * 2 * mp.pi
        # independent numeric: integrate v(1-d kappa) over [0,2pi]
        def integrand(t):
            x1 = -a * mp.sin(t); y1 = mp.cos(t)
            x2 = -a * mp.cos(t); y2 = -mp.sin(t)
            v = mp.sqrt(x1 ** 2 + y1 ** 2)
            kappa = (x1 * y2 - y1 * x2) / v ** 3
            return v * (1 - d3 * kappa)
        val = mp.quad(integrand, [0, 2 * mp.pi])
        out(f"  c={mp.nstr(c,3)} d={mp.nstr(d3,3)}: int v(1-dk)={mp.nstr(val,20)} "
            f"P-2pi d={mp.nstr(offP,20)} resid={mp.nstr(abs(val-offP),5)}")
