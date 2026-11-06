# X2-02-crossings.py
# PLAN-jacobi-X2, step 2:
#  (a) positive calibration: the abutting-arcs crossing realises ellipticEAm (E-inverse), 20+ digits;
#  (b) the autonomy/ODE test on natural crossing families whose parameter depends on u;
#  (c) the circularity demonstration: the parameter that DOES produce am already contains am.
# mpmath parameter convention m = c.
from mpmath import (mp, mpf, ellipfun, ellipf, ellipe, ellipk, sin, cos, sqrt, quad, pi,
                    atan2, findroot, nstr)

mp.dps = 40

def am(u, c):
    # am via atan2(sn,cn) (verified in X2-01 to 40 digits)
    return atan2(ellipfun('sn', u, c), ellipfun('cn', u, c))

def EAm(L, c):
    # inverse of incomplete E in its angle argument: solve ellipe(phi,c)=L
    return findroot(lambda p: ellipe(p, c) - L, pi/2, tol=mpf('1e-35'))

print("== (a) Positive calibration: abutting-arc crossing gives ellipticEAm ==")
print("   arc A  = ellipseParam b over [0,phi],   length E(phi,c);")
print("   arc B  = ellipseCoParam b over [0,pi/2-phi], length K - E(phi,c);")
print("   endpoints coincide at (sin phi, b cos phi), phi = EAm(L).")
worst = mpf(0)
for c in [mpf('0.3'), mpf('0.7'), mpf('0.93')]:
    b = sqrt(1 - c)
    K = ellipe(pi/2, c)   # E(pi/2), the co-arc's total length
    for frac in [mpf('0.2'), mpf('0.55'), mpf('0.9')]:
        L = frac * K
        phi = EAm(L, c)                          # the amplitude of E, independently computed
        # arc A length by quadrature (ellipseParam speed is sqrt(1-c sin^2))
        lenA = quad(lambda t: sqrt(1 - c*sin(t)**2), [0, phi])
        # co-arc B length by quadrature (ellipseCoParam speed is sqrt(1-c cos^2))
        lenB = quad(lambda t: sqrt(1 - c*cos(t)**2), [0, pi/2 - phi])
        # the crossing endpoint point, reconstructed from its coordinates:
        x, y = sin(phi), b*cos(phi)
        phi_rec = atan2(x, y/b)
        worst = max(worst, abs(lenA - L), abs(lenB - (K - L)), abs(phi_rec - phi))
    print(f"   c={nstr(c,4)}: worst (|lenA-L|,|lenB-(K-L)|,|phi_rec-phi|) = {nstr(worst,18)}")
print(f"   overall worst discrepancy = {nstr(worst,18)}  (mp.dps=40)")
print("   uniqueness: on [0,pi/2], sin is injective, so the shared endpoint is the only crossing.")
print()

print("== (b) Autonomy/ODE test on crossing families z(u) ==")
print("   PASS iff  (z')^2 == 1 - c sin^2 z  and z(0)=0  (Jacobi field dn).")
print("   We compute z(u) from the implicit crossing and z'(u) by implicit differentiation.")

def test_ode(name, zfun, zpfun, c, us):
    mx = mpf(0)
    for u in us:
        z = zfun(u); zp = zpfun(u)
        mx = max(mx, abs(zp**2 - (1 - c*sin(z)**2)))
    tag = "PASS" if mx < mpf('1e-15') else "fail"
    print(f"   {name:52s} c={nstr(c,3)}  max|z'^2-(1-c sin^2 z)|={nstr(mx,6)}  [{tag}]")
    return mx

cs = [mpf('0.3'), mpf('0.7'), mpf('0.93')]
us = [mpf('0.05'), mpf('0.3'), mpf('0.9')]

# Candidate 1: Kepler crossing sin(z-u) = a z  (sin curve translated by u, crossed with line)
for c in cs:
    for a in [mpf('0.2'), mpf('0.5')]:
        def zk(u, c=c, a=a):
            return findroot(lambda z: sin(z-u) - a*z, mpf('0.0'), tol=mpf('1e-30'))
        def zpk(u, c=c, a=a):
            z = zk(u); czu = cos(z-u)
            return czu/(czu - a)
        test_ode(f"Kepler: sin(z-u)=a z, a={nstr(a,3)}", zk, zpk, c, us)

# Candidate 2: sine curve scaled in x by 1/s, s=u: sin(z/u)=a z
for c in cs:
    for a in [mpf('0.3')]:
        def zs(u, c=c, a=a):
            return findroot(lambda z: sin(z/u) - a*z, mpf('0.0'), tol=mpf('1e-25'))
        def zps(u, c=c, a=a):
            z = zs(u); w = z/u
            # d/du [sin(z/u)] = cos(w)*(z'u - z)/u^2 = a z'
            denom = cos(w)/u - a
            return cos(w)*(-z/u**2)/denom
        test_ode(f"scaled: sin(z/u)=a z", zs, zps, c, us)

# Candidate 3: pendulum portrait crossed with a moving horizontal line p = p0 + u
#   p0^2 = 2k(cos th - cos th0); crossing p = p0+u gives cos th = cos th0 + (p0+u)^2/(2k)
for c in cs:
    k = mpf('1.0'); th0 = mpf('1.2'); p0 = mpf('0.3')
    def zth(u, c=c, k=k, th0=th0, p0=p0):
        return mp.acos(cos(th0) + (p0+u)**2/(2*k))
    def zpth(u, c=c, k=k, th0=th0, p0=p0):
        return -( (p0+u)/k ) / sqrt(1 - (cos(th0)+(p0+u)**2/(2*k))**2)
    test_ode("pendulum portrait & p=p0+u", zth, zpth, c, us)

# Candidate 4: tangent/vertical construction: ellipse co-arc endpoint angle vs u.
#   lay arc of length L=u on the ellipse from 0 -> angle EAm(u). Test whether that is am(u,u-link).
for c in cs:
    b = sqrt(1-c)
    def ze(u, c=c):
        return EAm(u, c)
    def zpe(u, c=c):
        return 1/sqrt(1 - c*sin(ze(u))**2)   # derivative of EAm is 1/dn -- inverse of dn
    test_ode("ellipse arc endpoint angle = EAm(u)", ze, zpe, c, [mpf('0.2'), mpf('0.5'), mpf('0.8')])
print()

print("== (c) Circularity: the vertical shift that DOES force am ==")
print("   Cross y = sin x + v(u) with y = a x. Then sin z + v = a z, so z' = v'/(a - cos z).")
print("   Requiring z = am gives v(u) = a*am(u) - sin(am(u)), i.e. v already contains am.")
for c in cs[:1]:
    a = mpf('0.4')
    mx = mpf(0)
    for u in [mpf('0.1'), mpf('0.4'), mpf('0.8')]:
        v = a*am(u, c) - sin(am(u, c))
        # solve sin z + v = a z for z near am(u)
        z = findroot(lambda z: sin(z) + v - a*z, am(u, c), tol=mpf('1e-30'))
        mx = max(mx, abs(z - am(u, c)))
    print(f"   c={nstr(c,3)}: reconstructed |z-am(u)| with v(u)=a am - sin am : {nstr(mx,18)}")
print("   v(u) = a*F^{-1}(u) - sin(F^{-1}(u)) is not in the allowed class (it is an expression")
print("   in the very inverse being constructed).")
print("DONE X2-02")
