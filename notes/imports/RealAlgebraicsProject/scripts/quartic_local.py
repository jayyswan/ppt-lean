"""Session 10: local analysis of the quartic step y = s' + t (s^2)' with Q4(y) = 0.

Checks, for E = (Z/2)^3 and H = Z/4 x Z/2 (regular on points 2..9, fixing point 1):
 A. eigenlines [e] of P(V): the fibre t-roots of Q4(e + t (e^2)') are finite and nonzero
 B. near L_1 = C x2, x2 = (8,-1,...,-1): with s = x2 + eps n, the four roots satisfy
    (1 + 7t)/eps -> roots of phi_n(tau) = Q4(tau x2 + (9/7) n), and phi has no root at 0 or infinity
 C. phi at the E- and H-eigen normal directions, exactly (sympy)
Run: python3 quartic_local.py
"""
import itertools, sympy as sp, cypari
pari = cypari.pari

def pw(x, k): return sum(v**k for v in x)
def tf(v): m = sum(v) / len(v); return [a - m for a in v]
def Q4(y): return 6*pw(y, 4) - pw(y, 2)**2

# characters of E = F_2^3 and H = Z/4 x Z/2 on the 8 moved points, point 1 fixed (coordinate 0)
E_pts = list(itertools.product([0, 1], repeat=3))
H_pts = [(i, j) for i in range(4) for j in range(2)]
def E_vec(c): return [0] + [(-1)**sum(a*b for a, b in zip(c, p)) for p in E_pts]
def H_vec(a, b): return [0] + [sp.I**(a*i) * (-1)**(b*j) for i, j in H_pts]
eig = {('E', c): E_vec(c) for c in E_pts if c != (0, 0, 0)}
eig.update({('H', a, b): H_vec(a, b) for a in range(4) for b in range(2) if (a, b) != (0, 0)})

t, tau, c = sp.symbols('t tau c')
x2 = [8] + [-1]*8

print('A. eigenline fibres Q4(e + t (e^2)\'), and the character order of e')
for k, e in eig.items():
    w = tf([sp.expand(v**2) for v in e])
    q = sp.Poly(sp.expand(Q4([a + t*b for a, b in zip(e, w)])), t)
    co = q.all_coeffs()
    print('  ', k, ' t^4 coeff', sp.nsimplify(co[0]), ' t^0 coeff', sp.nsimplify(co[-1]),
          ' roots nonzero finite:', co[0] != 0 and co[-1] != 0)

print('C. phi(tau) = Q4(tau x2 + c n) at eigen normal directions n')
seen = set()
for k, e in eig.items():
    phi = sp.factor(sp.expand(Q4([tau*a + c*b for a, b in zip(x2, e)])))
    if str(phi) in seen: continue
    seen.add(str(phi))
    disc = sp.factor(sp.discriminant(sp.expand(phi), tau))
    print('  ', k, ' phi =', phi, '  disc_tau =', disc)

print('B. numerical: roots of Q4(s\' + t (s^2)\') near L_1, s = x2 + eps n')
import random
rnd = random.Random(10)
for trial in range(3):
    n = tf([pari(0)] + [pari(rnd.randint(-9, 9)) for _ in range(8)])
    n = [pari(0)] + [v - sum(n[1:]) / 8 for v in n[1:]]   # normal: first coord 0, trace 0
    phi = Q4([pari('x')*a + pari('9/7')*b for a, b in zip(x2, n)])
    target = sorted(pari.polroots(phi), key=lambda z: (float(z.real()), float(z.imag())))
    for eps in ['1/10^4', '1/10^6']:
        e_ = pari(eps)
        s = [a + e_*b for a, b in zip(x2, n)]
        w = tf([v**2 for v in s])
        q = Q4([a + pari('x')*b for a, b in zip(s, w)])
        rts = sorted([(1 + 7*r)/e_ for r in pari.polroots(q)], key=lambda z: (float(z.real()), float(z.imag())))
        err = max(abs(a - b) for a, b in zip(rts, target))
        print('   trial %d eps %s  max |(1+7t)/eps - phi root| = %.2e' % (trial, eps, float(err)))
