# Session 63 (S63.3): planted rational member of the row-B5 family over Q.
# Take a real point of L_135^(10) (10 reals, p1=p3=p5=0), round E, R, zeta to rationals keeping
# E(zeta^2) + R(zeta) = 0 exactly; g = (E(w^2)+R(w))/(w - zeta) is a totally real rational nonic
# whose root field K has the Q-point u = w on V_K: Tr u^3 = (Tr u)^3, Tr u^5 = (Tr u)^5.
# Usage: python3 plant63.py <seed> [den]
import sys, numpy as np, cypari
from fractions import Fraction as Fr
pari = cypari.pari
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
den = int(sys.argv[2]) if len(sys.argv) > 2 else 50
rng = np.random.default_rng(seed)

def newton_pt():
    while True:
        y = rng.normal(size=10)
        for _ in range(100):
            F = np.array([np.sum(y**k) for k in (1, 3, 5)])
            J = np.array([k*y**(k-1) for k in (1, 3, 5)])
            dy = np.linalg.lstsq(J, -F, rcond=None)[0]
            y = y + dy
            if np.linalg.norm(F) < 1e-13: break
        if np.linalg.norm([np.sum(y**k) for k in (1, 3, 5)]) < 1e-11 and np.min(np.diff(np.sort(y))) > 0.05:
            return y
y = newton_pt()
y = y / np.max(np.abs(y)) * 3
zeta_f = y[0]
c = np.poly(y)                       # degree 10, c[0] = 1
# even part E(w^2): coefficients c[0], c[2], ..., c[10]; odd part R: c[7] w^3 + c[9] w
Ec = [Fr(round(c[2*k]*den), den) for k in range(6)]      # E(V) = sum Ec[k] V^(5-k)
Ec[0] = Fr(1)
r3 = Fr(round(c[7]*den), den)
zeta = Fr(round(zeta_f*den), den)
EV = sum(Ec[k]*zeta**(2*(5-k)) for k in range(6))
r1 = (-EV - r3*zeta**3)/zeta
pari('w')
E_str = '+'.join('(%s)*w^%d' % (Ec[k], 2*(5-k)) for k in range(6))
f = pari('(%s)+(%s)*w^3+(%s)*w' % (E_str, r3, r1))
g = pari('(%s)/(w-(%s))' % (f, zeta))
g = g * pari('denominator(content(%s))' % g)
print('g =', g)
print('irreducible:', pari.polisirreducible(g), ' real roots:', pari.polsturm(g))
# Frobenius cycle types (degree 9): look for a 9-cycle, an (8,1) and a (7,2) or (7,1,1)
types = {}
D = pari.poldisc(g)
p = 2
while len(types) < 40 and p < 3000:
    p = int(pari.nextprime(p+1))
    if pari('(%s)%%%d' % (D, p)) == 0 or pari('pollead(%s)%%%d' % (g, p)) == 0: continue
    fa = pari.factormod(g, p)
    t = tuple(sorted([int(pari.poldegree(fa[0][i])) for i in range(len(fa[0])) for _ in range(int(fa[1][i]))], reverse=True))
    types[t] = types.get(t, 0) + 1
print('cycle types:', sorted(types.items(), key=lambda kv: -kv[1])[:12])
print('disc square?', pari('issquare')(D))
# check the Q-point on V_K: u = class of w (root theta); p3^(10), p5^(10) with zeta' = -Tr u
rts = np.roots([float(x) for x in pari.Vec(g)])
rts = np.real(rts)
t = rts.sum()
print('Tr u^3 - (Tr u)^3 =', np.sum(rts**3) - t**3, '  Tr u^5 - (Tr u)^5 =', np.sum(rts**5) - t**5,
      '  -Tr u =', -t, ' zeta =', float(zeta))
