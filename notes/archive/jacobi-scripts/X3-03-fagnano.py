# X3-03-fagnano.py -- Fagnano's theorem is the addition theorem for E (2nd kind);
# the first-kind analogue (lemniscate/Fagnano doubling) exists only at m = 1/2.
import mpmath as mp
from mpmath import mpf, sqrt, sin, cos, atan2

mp.mp.dps = 32
E = lambda ph, m: mp.ellipe(ph, m)
F = lambda ph, m: mp.ellipf(ph, m)

# --- (A) Euler / Fagnano addition theorem for the 2nd kind ---
# If F(phi)+F(psi)=F(mu) (Jacobi sn-addition), then
#     E(phi)+E(psi)-E(mu) = m * sin(phi) sin(psi) sin(mu)   [algebraic straight length]
def mu_of(ph, ps, m):
    sph, cph, sps, cps = sin(ph), cos(ph), sin(ps), cos(ps)
    dph, dps = sqrt(1-m*sph*sph), sqrt(1-m*sps*sps)
    den = 1 - m*sph*sph*sps*sps
    return atan2((sph*cps*dps + sps*cph*dph)/den,
                 (cph*cps - sph*sps*dph*dps)/den)

print("(A) Fagnano/Euler E-addition  E(phi)+E(psi)-E(mu) = m sin phi sin psi sin mu")
worst = 0
for m in [mpf('0.3'), mpf('0.6'), mpf('0.85')]:
    for (ph, ps) in [(mpf('0.4'), mpf('0.7')), (mpf('0.9'), mpf('0.3')),
                     (mpf('1.1'), mpf('0.5'))]:
        mu = mu_of(ph, ps, m)
        lhs = E(ph, m)+E(ps, m)-E(mu, m)
        rhs = m*sin(ph)*sin(ps)*sin(mu)
        worst = max(worst, abs(lhs-rhs))
        print("   m=%4.2f  phi=%4.2f psi=%4.2f  residual = %s"
              % (m, ph, ps, mp.nstr(lhs-rhs, 4)))
print("   worst residual over 9 cases:", mp.nstr(worst, 4),
      "  -> [symbolic] identity confirmed numerically")
print("   the RHS is algebraic: an arc difference equals a straight length (Fagnano).")

# --- (B) the first-kind analogue: lemniscate doubling, modulus locked at m=1/2 ---
print("\n(B) lemniscate (m=1/2): sl(2u)=2 sl(u) sqrt(1-sl^4)/(1+sl^4), modulus locked")
def lemn_u(r):                      # u = int_0^r dt/sqrt(1-t^4)
    return mp.quad(lambda t: 1/sqrt(1-t**4), [0, r])
def lemn_r(u):                      # invert
    lo, hi = mpf(0), mpf('0.999999')
    for _ in range(120):
        mid = (lo+hi)/2
        if lemn_u(mid) < u: lo = mid
        else: hi = mid
    return (lo+hi)/2
for u in [mpf('0.3'), mpf('0.6'), mpf('0.9')]:
    r = lemn_r(u)
    lhs = lemn_r(2*u)
    rhs = 2*r*sqrt(1-r**4)/(1+r**4)
    print("   u=%4.2f  sl(2u)=%s  formula=%s  diff=%s"
          % (u, mp.nstr(lhs, 12), mp.nstr(rhs, 12), mp.nstr(lhs-rhs, 3)))
# the lemniscate integral has the single fixed parameter m=1/2; R2 showed affine
# scaling cannot change it.  So the 1st-kind geometric addition is c=1/2 only.

# --- (C) general first-kind addition IS available algebraically, but is addition ---
print("\n(C) general Jacobi sn-addition (algebraic, any m) - but it needs am(u), am(v) as input:")
m = mpf('0.7')
for (u, v) in [(mpf('0.4'), mpf('0.9')), (mpf('0.7'), mpf('1.3'))]:
    def sn(x): return mp.ellipfun('sn', x, m)
    def cn(x): return mp.ellipfun('cn', x, m)
    def dn(x): return mp.ellipfun('dn', x, m)
    lhs = sn(u+v)
    rhs = (sn(u)*cn(v)*dn(v) + sn(v)*cn(u)*dn(u))/(1-m*sn(u)**2*sn(v)**2)
    print("   m=0.7 u=%4.2f v=%4.2f  sn(u+v) residual = %s"
          % (u, v, mp.nstr(lhs-rhs, 4)))
print("   => geometric/algebraic addition exists; it does not invert F, so it gives no am.")
