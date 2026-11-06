# X2-01-basics.py
# PLAN-jacobi-X2, step 1: Pfaffian chain, am = atan2(sn,cn), the exact equation for am,
# and the pendulum phase portrait (time vs Euclidean arc length).
# mpmath convention: ellipfun(kind, u, m) and ellipf(phi, m) take the PARAMETER m = c = k^2.
from mpmath import mp, mpf, ellipfun, ellipf, ellipk, ellipe, ellipfun, sin, cos, sqrt, quad, pi, atan2, nstr

mp.dps = 40

def report(name, val):
    print(f"{name}: {nstr(val, 25)}")

print("== Pfaffian chain X=(sn,cn,dn): X' = polynomial(X) ==")
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    worst = mpf(0)
    for u in [mpf('0.1'), mpf('0.77'), mpf('1.3')]:
        h = mpf('1e-20')
        sn = ellipfun('sn', u, c); cn = ellipfun('cn', u, c); dn = ellipfun('dn', u, c)
        snp = (ellipfun('sn', u+h, c) - ellipfun('sn', u-h, c))/(2*h)
        cnp = (ellipfun('cn', u+h, c) - ellipfun('cn', u-h, c))/(2*h)
        dnp = (ellipfun('dn', u+h, c) - ellipfun('dn', u-h, c))/(2*h)
        worst = max(worst, abs(snp - cn*dn), abs(cnp + sn*dn), abs(dnp + c*sn*cn))
    report(f"c={nstr(c,4)} worst Pfaffian residual", worst)

print()
print("== am = atan2(sn, cn) (so position on the circle determines the amplitude) ==")
# am is, by definition, the inverse of F: solve F(phi,c)=u for phi in [0,2K] by bisection.
def am_via_F(u, c):
    twoK = 2*ellipk(c)
    lo, hi = mpf(0), twoK
    # shift u into [0, 2K] by the (2K, pi) quasi-period -- here just reduce modulo 4K enough
    uu = u - mp.floor(u/(2*twoK))*2*twoK  # in [0,2K)
    lo, hi = mpf(0), twoK
    for _ in range(400):
        mid = (lo+hi)/2
        if ellipf(mid, c) < uu: lo = mid
        else: hi = mid
    return (lo+hi)/2
worst = mpf(0)
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    for u in [mpf('0.1'), mpf('0.77'), mpf('1.3'), mpf('2.9')]:
        sn = ellipfun('sn', u, c); cn = ellipfun('cn', u, c)
        am = atan2(sn, cn)
        # independent am: reduce u into [0,2K] then bisect; atan2 branch is in (-pi,pi],
        # so compare against am_via_F shifted to (-pi,pi].
        amv = am_via_F(u, c)
        amv = ((amv + pi) % (2*pi)) - pi
        d = (am - amv) % (2*pi)
        if d > pi: d -= 2*pi
        worst = max(worst, abs(d))
report("worst |atan2(sn,cn)-am| mod 2pi", worst)

print()
print("== Exact equation for am: u = F(am(u), c) ==")
worst = mpf(0)
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    for u in [mpf('0.1'), mpf('0.77'), mpf('1.3'), mpf('2.9')]:
        amv = atan2(ellipfun('sn', u, c), ellipfun('cn', u, c))
        # reduce F(am) modulo the period 2F(pi)=4K and compare modulo 4K
        d = (ellipf(amv, c) - u) % (4*ellipk(c))
        if d > 2*ellipk(c): d -= 4*ellipk(c)
        worst = max(worst, abs(d))
report("worst |F(atan2(sn,cn)) - u| mod 4K", worst)

print()
print("== F is NOT a finite trigonometric polynomial in phi ==")
# F(phi) = int_0^phi dtheta/sqrt(1-c sin^2 theta). Expand the integrand in cos(2k theta):
#   1/sqrt(1-c sin^2) = sum_{k>=0} a_k cos(2k theta), all a_k != 0 for 0<c<1.
# Fit a finite Fourier (cos 2k) ansatz to u = F(phi) for phi in [0, pi/2] and show the
# residual does not go to zero as the number of terms grows (it is a genuine infinite series).
import numpy as np
for c in [mpf('0.3'), mpf('0.7')]:
    phi_grid = [mpf(str(t)) for t in np.linspace(0.05, 1.5, 60)]
    target = [ellipf(p, c) for p in phi_grid]
    print(f"  c={nstr(c,4)}: finite fit u = sum_{{k=0..N}} a_k cos(2k phi)")
    for N in [1, 2, 3, 5, 8, 12]:
        # least squares over grid, basis {1, cos2phi,...,cos(2N phi)}
        A = np.array([[float(cos(2*k*p)) for k in range(N+1)] for p in phi_grid])
        b = np.array([float(t) for t in target])
        coef, res, rank, sv = np.linalg.lstsq(A, b, rcond=None)
        r = np.linalg.norm(A@coef - b, np.inf)
        print(f"    N={N:2d}   max residual = {r:.3e}   a_{N} = {coef[-1]: .6e}")

print()
print("== Pendulum: time integral vs Euclidean arc length of the phase portrait ==")
# Phase portrait: p^2 = 2k (cos th - cos th0), th in [-th0, th0]. Time to go th0 -> th:
#   t(th) = int_th0^th dphi / sqrt(2k(cos phi - cos th0)).
# This equals (1/sqrt(k)) * F(psi, sin^2(th0/2)) with sin psi = sin(th/2)/sin(th0/2).
# Euclidean arc length of the portrait: dsigma = sqrt(1+(dp/dth)^2) dth.
for k in [mpf('1.0'), mpf('2.0')]:
    th0 = mpf('1.2')
    sm = sin(th0/2)
    print(f"  k={nstr(k,3)}, th0={nstr(th0,4)}:")
    for th in [mpf('0.2'), mpf('0.6'), mpf('1.0')]:
        # time from th UP to th0 (positive)
        t_int = quad(lambda phi: 1/sqrt(2*k*(cos(phi)-cos(th0))), [th, th0])
        psi = mp.asin(sin(th/2)/sm)
        t_f = (ellipk(sm**2) - ellipf(psi, sm**2))/sqrt(k)
        # Euclidean arc length of the (th, p) portrait, same interval
        s_int = quad(lambda phi: sqrt(1 + (k*sin(phi)/sqrt(2*k*(cos(phi)-cos(th0))))**2),
                     [th, th0])
        print(f"    th={nstr(th,3)}  t_time={nstr(t_int,18)}  t_F={nstr(t_f,18)}  "
              f"euclidean_len={nstr(s_int,18)}  ratio(time/len)={nstr(t_int/s_int,18)}")
print("   (time is an F-integral; the Euclidean arc length of the portrait is a DIFFERENT,")
print("    elementary-looking integral; the ratio is neither 1 nor a constructible-free value)")

print()
print("== Q3: most elementary finite 'Kepler-like' equation for am ==")
# Exact: u = F(phi,c). First-order expansion of the integrand gives the Kepler form
#   u = (1 + c/4 + 9c^2/64 + ...) phi - (c/8 + c^2/16 + ...) sin(2 phi) + ...
# Test the 1-term Kepler fit u = a phi + b sin(2 phi) and the 2-term fit.
for c in [mpf('0.1'), mpf('0.3'), mpf('0.7')]:
    phi_grid = [mpf(str(t)) for t in np.linspace(0.02, 1.4, 200)]
    target = [ellipf(p, c) for p in phi_grid]
    print(f"  c={nstr(c,4)}:")
    for basis_name, basis in [("Kepler  a*phi + b*sin2phi",
                               lambda p: [p, sin(2*p)]),
                              ("2-term  ...+ d*sin4phi",
                               lambda p: [p, sin(2*p), sin(4*p)]),
                              ("3-term  ...+ e*sin6phi",
                               lambda p: [p, sin(2*p), sin(4*p), sin(6*p)])]:
        A = np.array([[float(v) for v in basis(p)] for p in phi_grid])
        b = np.array([float(t) for t in target])
        coef, *_ = np.linalg.lstsq(A, b, rcond=None)
        r = np.linalg.norm(A@coef - b, np.inf)
        cs = " ".join(f"{x: .4e}" for x in coef)
        print(f"    {basis_name:28s} residual={r:.3e}  coefs=[{cs}]")
print("DONE X2-01")
