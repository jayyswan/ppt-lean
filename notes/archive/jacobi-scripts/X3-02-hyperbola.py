# X3-02-hyperbola.py -- MacCullagh / Landen: a hyperbola arc is a MIX of E and F.
# Hyperbola x = a cosh(t), y = b sinh(t)  (right branch),  c^2 = a^2+b^2.
#     ds = sqrt(b^2 + c^2 sinh^2 t) dt.
# MathWorld: s(t) = -i b E(i t, k_c),  k_c = c/b  (modulus).
# Convert with DLMF 19.7.7 (imaginary argument) + 19.7.5 (imaginary modulus):
#     k0 = a/b,  kappa = a/c,  kappa' = b/c,
#     sinh t = tan(psi),   sin(theta) = sqrt(1+k0^2) sin(psi)/sqrt(1+k0^2 sin^2 psi),
#     s(t) = (b^2/c) F(theta,kappa) - c E(theta,kappa)
#            + (a^2/c) sin(theta)cos(theta)/sqrt(1-kappa^2 sin^2 theta)
#            + b tan(psi) sqrt(1+k0^2 sin^2 psi).
# E-coefficient (-c) and F-coefficient (b^2/c) are BOTH nonzero -> a genuine mix.
import mpmath as mp
from mpmath import mpf, sqrt, sin, cos, tan, atan, pi

mp.mp.dps = 30
a = mpf(2); b = mpf(1); c = sqrt(a*a + b*b)
k0 = a/b; kap = a/c; kapp = b/c; kap2 = kap*kap

def s_direct(t):
    return mp.quad(lambda u: sqrt(b*b + c*c*mp.sinh(u)**2), [0, t])

def s_formula(t):
    psi = atan(mp.sinh(t))                 # sinh t = tan psi
    s2p = sin(psi)**2
    sth = sqrt(1+k0*k0)*sin(psi)/sqrt(1+k0*k0*s2p)
    cth = sqrt(1 - sth*sth)
    F = mp.ellipf(mp.asin(sth), kap2)
    E = mp.ellipe(mp.asin(sth), kap2)
    alg = (a*a/c)*sth*cth/sqrt(1-kap2*sth*sth) + b*tan(psi)*sqrt(1+k0*k0*s2p)
    return (b*b/c)*F - c*E + alg

print("a,b =", a, b, "c =", mp.nstr(c,12), " kappa = a/c =", mp.nstr(kap,12))
print("\n(A) reduction check  s_formula - s_direct:")
for t in [mpf('0.3'), mpf('0.8'), mpf('1.5'), mpf('2.5')]:
    print("   t=%4.2f  diff = %s" % (t, mp.nstr(s_formula(t)-s_direct(t), 5)))

print("\n(B) the two elliptic coefficients (nonzero both):")
print("   F-coefficient = b^2/c =", mp.nstr(b*b/c, 12))
print("   E-coefficient = -c    =", mp.nstr(-c, 12))

# (C) inverse of the mixed map is not the amplitude
def theta_of(psi):
    s2p = sin(psi)**2
    sth = sqrt(1+k0*k0)*sin(psi)/sqrt(1+k0*k0*s2p)
    return mp.asin(sth)

target = s_formula(mpf('1.0'))
theta_true = theta_of(mpf('1.0'))
lo, hi = mpf('1e-9'), mpf(pi/2) - mpf('1e-9')
for _ in range(140):
    mid = (lo+hi)/2
    if s_formula(mid) < target: lo = mid
    else: hi = mid
psi_rec = (lo+hi)/2
theta_rec = theta_of(psi_rec)
beta = b*b/c
am_guess = mp.atan2(mp.ellipfun('sn', target/beta, kap2),
                    mp.ellipfun('cn', target/beta, kap2))
print("\n(C) mixed-map inversion (target = s at psi=1.0):")
print("   recovered theta =", mp.nstr(theta_rec, 15), " true =", mp.nstr(theta_true, 15))
print("   am(target/beta) =", mp.nstr(am_guess, 15), "  (NOT the recovered angle)")
print("   => the inverse of the mixed arc is neither F nor am; it is a new transcendental map.")

# (D) can a drawable curve supply the missing pure-F piece? ellipse arc coefficient:
print("\n(D) ellipse arcs contribute E only (F-coefficient 0); hyperbola needs F with")
print("    coefficient b^2/c != 0.  E-parts may cancel, the F-part cannot - it has no")
print("    drawable partner (R1/R2: no drawable curve has first-kind arclength).")
