"""Session 8 checks (Nov 16, 2026).

g6 = 231 p2^3 - 966 p2 p4 + 1008 p6 - 256 p3^2 on V = trace-zero part of C^9.
Run: python3 session8_checks.py   (needs numpy, scipy, sympy)
The abelian 2-subgroup check for D is separate: ab2.g (GAP) then ab2fix.py.
"""
import numpy as np, sympy as sp
from scipy.optimize import minimize

def p(x, k): return np.sum(x**k)
def f4(x): return 24*p(x, 4) - 19*p(x, 2)**2
def g6(x): return 231*p(x, 2)**3 - 966*p(x, 2)*p(x, 4) + 1008*p(x, 6) - 256*p(x, 3)**2

# 1. Uniqueness: g6 is the only symmetric sextic (p1 = 0) vanishing on all vectors with 7 equal coordinates.
a, b = sp.symbols('a b'); A = sp.symbols('A0:4')
x = [a]*7 + [b, -7*a - b]
ps = lambda k: sp.expand(sum(v**k for v in x))
f = A[0]*ps(2)**3 + A[1]*ps(2)*ps(4) + A[2]*ps(6) + A[3]*ps(3)**2
print('1. sextics vanishing on (a^7,b,c):', sp.solve(sp.Poly(f, a, b).coeffs(), A, dict=True))

# 2. Order of vanishing along L_j and the normal quartic at H-eigenvectors.
x2 = np.array([8.] + [-1.]*8)
H = [(i, j) for i in range(4) for j in range(2)]
e4 = np.array([0] + [1j**i for i, j in H])          # order-4 character of Z/4 x Z/2
e2 = np.array([0] + [(-1.)**i for i, j in H])       # order-2 character
def taylor(fun, base, n, K=7):
    r = 0.5; th = np.exp(2j*np.pi*np.arange(16)/16)
    c = np.fft.fft([fun(base + r*t*n) for t in th])/16
    return np.array([c[k]/r**k for k in range(K)])
rng = np.random.default_rng(0)
n = np.r_[0, rng.normal(size=8)]; n[1:] -= n[1:].mean()
print('2. |coeff eps^k| of g6(x2 + eps n), k=0..6:', np.round(np.abs(taylor(g6, x2, n)), 3))
print('   normal quartic of g6 at e4:', np.round(taylor(g6, x2, e4)[4].real, 3),
      ' at e2:', np.round(taylor(g6, x2, e2)[4].real, 3))
print('   normal quadric of f4 at e4:', np.round(taylor(f4, x2, e4)[2].real, 3),
      ' at e2:', np.round(taylor(f4, x2, e2)[2].real, 3))
print('   values on eigenlines: p2(e2) =', p(e2, 2), ' p2(e4) =', p(e4, 2),
      ' f4(e4) =', f4(e4).real, ' g6(e4) =', g6(e4).real)

# 3. Nonnegativity of g6 on real V (numerical): minimise g6/p2^3 from random starts.
def R(y):
    x = np.r_[y, -y.sum()]; return g6(x)/p(x, 2)**3
vals = [minimize(R, rng.normal(size=8), method='BFGS', options={'gtol': 1e-13}).fun for _ in range(500)]
X = rng.normal(size=(100000, 9)); X -= X.mean(1, keepdims=True)
print('3. min of g6/p2^3: over 500 local minimisations %.2e; over 1e5 random points %.4f'
      % (min(vals), min(g6(x)/p(x, 2)**3 for x in X)))

# 4. The (4,4,1) plane: Q4 and Q5 have no common zero; p2, f4, g6 do not vanish identically.
x = [a]*4 + [b]*4 + [-4*a - 4*b]
ps = lambda k: sp.expand(sum(v**k for v in x))
Q4 = 6*ps(4) - ps(2)**2; Q5 = 18*ps(5) - 5*ps(2)*ps(3)
print('4. Res(Q4,Q5) on (4,4,1) plane:', sp.resultant(Q4.subs(b, 1), Q5.subs(b, 1), a))
print('   p2, f4, g6 there:', sp.factor(ps(2)), '|', sp.factor(24*ps(4) - 19*ps(2)**2), '|',
      sp.factor(231*ps(2)**3 - 966*ps(2)*ps(4) + 1008*ps(6) - 256*ps(3)**2))
