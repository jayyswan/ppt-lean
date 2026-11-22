# Session 62: end-to-end check of row B5 on L135 (r = 9).
# Finds a real point u of Omega_0 = L135 cap {B2 = 0} (p1=p3=p5=0, p2^3-15p2p4+50p6=0) by Newton,
# builds E (even part of w*chi_u), R (odd part), the affine map taking y = x^5 - x^3 to y = E(x) + linear,
# and checks that the Bezier (t^2, Y(t)) crosses the mapped graph exactly at t in {u_i} U {0}.
# Usage: python3 b5plant.py <seed>
import sys, numpy as np
rng = np.random.default_rng(int(sys.argv[1]))
def F(z):
    p = lambda k: np.sum(z**k)
    return np.array([p(1), p(3), p(5), p(2)**3 - 15*p(2)*p(4) + 50*p(6)])
for attempt in range(200):
    z = rng.normal(size=9)
    for it in range(100):
        J = np.zeros((4, 9)); f0 = F(z)
        for i in range(9):
            d = np.zeros(9); d[i] = 1e-7; J[:, i] = (F(z + d) - f0)/1e-7
        z = z - np.linalg.pinv(J) @ f0
    if np.abs(F(z)).max() < 1e-11 and min(abs(a - b) for i, a in enumerate(z) for b in z[i+1:]) > 1e-3 and min(abs(z)) > 1e-3:
        break
print('attempt', attempt, 'residual', np.abs(F(z)).max())
print('u =', np.round(np.sort(z), 6))
c = np.poly(np.append(z, 0.0))           # w*chi_u(w), degree 10, coefficients high -> low
assert abs(c[1]) + abs(c[3]) + abs(c[5]) < 1e-9
Ecoef = c[0::2]                         # V^5 .. V^0  (from w^10, w^8, ..., w^0)
Rcoef = np.zeros(4); Rcoef[0] = c[7]; Rcoef[2] = c[9]   # odd part a7 w^3 + a9 w
# depress E: V = y + h, h = -a2/5
h = -Ecoef[1]/5
Ey = np.poly1d(Ecoef)(np.poly1d([1, h]))  # E(y + h) as poly in y
B3, B2 = Ey.coeffs[2], Ey.coeffs[3]
print('depressed E: y^4 %.2e  B3 %.6f  B2 %.2e' % (Ey.coeffs[1], B3, B2))
a = np.sqrt(-B3)                           # y = a x  =>  E = a^5 (x^5 - x^3) + linear(x) + const
# graph of S(x) = x^5 - x^3 under (x, y) -> (a x + h, a^5 y + m x + n): equals E(V) on the nose
m = Ey.coeffs[4]*a; n = Ey.coeffs[5]
def mapped(V):
    x = (V - h)/a
    return a**5*(x**5 - x**3) + m*x + n
Vt = rng.normal(size=5)
print('mapped quintic graph = E on 5 random V:', np.abs(mapped(Vt) - np.poly1d(Ecoef)(Vt)).max())
# Bezier: (X(t), Y(t)) = (t^2, -R(t)); crossings: mapped(t^2) - Y(t) = E(t^2) + R(t) = t*chi_u(t)
T = np.poly1d(Ecoef)(np.poly1d([1, 0, 0])) + np.poly1d(Rcoef)
roots = np.sort(np.roots(T.coeffs))
print('crossing parameters (real parts):', np.round(np.real(roots), 6))
print('max imag', np.abs(np.imag(roots)).max(), '  match {u_i} U {0}:',
      np.abs(np.sort(np.real(roots)) - np.sort(np.append(z, 0))).max())
print('class: S = x^5 - x^3 (B2 = 0, B3 < 0), affine dials a = %.6f, h = %.6f' % (a, h))
