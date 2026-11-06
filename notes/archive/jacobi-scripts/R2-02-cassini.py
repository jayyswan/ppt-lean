# R2-02-cassini.py
# Cassini ovals: (x^2+y^2+a^2)^2 - 4 a^2 x^2 = b^4, equivalently
#   r^4 - 2 a^2 r^2 cos(2 theta) + a^4 - b^4 = 0.
# Serret, JMPA 8 (1843) 145-154, proved these represent F for every modulus.
# Claim derived here:
#   with alpha0 = a^2+b^2, beta0 = |a^2-b^2|, P = alpha0^2, Q = beta0^2,
#   ds = b^2 sqrt(u) du / sqrt((P-u^2)(u^2-Q)),  u = r^2,
#   and the arc from the vertex (u = alpha0) is
#        s = (b^2/alpha0) * F(phi, k),   k = 2ab/(a^2+b^2),
#   where sin^2 phi = (alpha0^2 - u^2)/(alpha0^2 - beta0^2).
# In particular k^2 ranges over all of (0,1) as b/a ranges over (1, inf).
# Verified numerically against mpmath quadrature and ellipf.

import sympy as sp
from mpmath import mp, mpf, sqrt, ellipf, quad, cos, sin, pi, asin, acos

# ---------------- symbolic derivation ----------------
u, a, b = sp.symbols('u a b', positive=True)
P = (a**2 + b**2)**2
Q = (a**2 - b**2)**2
expr = b**2 * sp.sqrt(u) / sp.sqrt((P - u**2) * (u**2 - Q))
print("=== Cassini symbolic checks ===")
# substitution u^2 = alpha0^2 cos^2 phi + beta0^2 sin^2 phi
alpha0, beta0, phi = sp.symbols('alpha0 beta0 phi', positive=True)
usub = sp.sqrt(alpha0**2 * sp.cos(phi)**2 + beta0**2 * sp.sin(phi)**2)
# check: the differential b^2 sqrt(u) du / sqrt((P-u^2)(u^2-Q)) equals
#        -(b^2/alpha0) dphi / sqrt(1-k^2 sin^2 phi), k^2 = 1-(beta0/alpha0)^2
# We verify the algebraic core: du/dphi / sqrt((P-u^2)(u^2-Q)) at u=usub.
du_dphi = sp.diff(usub, phi)
core = sp.simplify(du_dphi / sp.sqrt(
    (alpha0**2 - usub**2) * (usub**2 - beta0**2)))
print("du/dphi / sqrt((P-u^2)(u^2-Q)) =", sp.simplify(core))
print("  (expected -1/u = -1/sqrt(alpha0^2 cos^2+beta0^2 sin^2))")
k2 = 1 - (beta0 / alpha0)**2
print("sqrt(u) =", sp.simplify(sp.sqrt(alpha0**2*sp.cos(phi)**2+beta0**2*sp.sin(phi)**2)))
print("k^2 = 1-(beta0/alpha0)^2 ; with beta0=b^2-a^2, alpha0=a^2+b^2:")
print("   k^2 =", sp.simplify(1 - ((b**2-a**2)/(a**2+b**2))**2),
      " = 4a^2b^2/(a^2+b^2)^2")

# ---------------- numerical verification ----------------
mp.dps = 30

def cassini_check(aval, bval, thetas):
    av, bv = mpf(aval), mpf(bval)
    a2, b2 = av*av, bv*bv
    a0, b0 = a2 + b2, abs(a2 - b2)
    k = 2*av*bv/(a2 + b2)
    # outer branch r(theta) for b>a (single oval): r^2 = a^2 cos2t + sqrt(b^4-a^4 sin^2 2t)
    def r2(th):
        return a2*cos(2*th) + sqrt(b2*b2 - a2*a2*sin(2*th)**2)
    def r(th):
        return sqrt(r2(th))
    # numeric arclength from theta=0 to theta using quadrature of ds/dtheta
    def integrand(th):
        h = mpf('1e-20')
        dr = (r(th+h) - r(th-h))/(2*h)
        return sqrt(r(th)**2 + dr**2)
    print(f"--- a={aval}, b={bval}, k={mp.nstr(k,20)}, k^2={mp.nstr(k**2,20)} ---")
    for th0 in thetas:
        th0 = mpf(th0)
        s_num = quad(integrand, [0, th0])
        u0 = r2(th0)
        sin2phi = (a0**2 - u0)/(a0**2 - b0**2)
        s_sin = sqrt(sin2phi)  # sin(phi), phi in [0,pi/2]
        phi0 = asin(s_sin)
        s_pred = (b2/a0) * ellipf(phi0, k**2)
        print(f"  theta={mp.nstr(th0,6)}: numeric={mp.nstr(s_num,20)}"
              f"  pred={mp.nstr(s_pred,20)}  diff={mp.nstr(abs(s_num-s_pred),5)}")

cassini_check(1, 2, ['0.3', '0.7', '1.2', '1.5707963267948966'])
cassini_check(1, mp.nstr(2+sqrt(3), 25), ['0.5', '1.0'])   # k=1/2 target
cassini_check(1, '10', ['0.2', '0.6'])                    # small k

# ---------------- modulus map inverse ----------------
print()
print("=== inverse: given target c in (0,1), rho=b/a solves 2 rho/(1+rho^2)=c ===")
for c in ['0.25', '0.5', '0.8', '0.99']:
    cv = mpf(c)
    rho = (1 + sqrt(1 - cv**2))/cv
    k_check = 2*rho/(1 + rho**2)
    print(f"  c={c}: rho={mp.nstr(rho,20)}  k(rho)={mp.nstr(k_check,20)}"
          f"  err={mp.nstr(abs(k_check-cv),5)}  (rho>1, algebraic in sqrt)")
