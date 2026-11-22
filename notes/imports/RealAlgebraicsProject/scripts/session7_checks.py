# Session 7: checks for the even-step analysis (Propositions J1-J3, Lemma K.1).
import numpy as np, itertools, sympy as sp
from scipy.optimize import minimize
rng = np.random.default_rng(0)
P = lambda x, k: np.sum(np.asarray(x)**k)
Q4 = lambda x: 6*P(x,4) - P(x,2)**2
Q5 = lambda x: 18*P(x,5) - 5*P(x,2)*P(x,3)
f4 = lambda x: 24*P(x,4) - 19*P(x,2)**2       # vanishes on the near-scalar lines

# (1) max of p4/p2^2 on real trace-zero vectors in R^9.  Critical points take <= 3 values.
best = (0, None)
for n1 in range(1, 9):
    for n2 in range(0, 9 - n1):
        n3 = 9 - n1 - n2
        def neg(v):
            a, b = v
            if n3 == 0:
                if n2 == 0: return 0
                c = None; x = [a]*n1 + [b]*n2
            else:
                c = -(n1*a + n2*b)/n3; x = [a]*n1 + [b]*n2 + [c]*n3
            x = np.array(x); x = x - x.mean()
            s = P(x,2)
            return 0 if s < 1e-12 else -P(x,4)/s**2
        for _ in range(20):
            r = minimize(neg, rng.normal(size=2), method='Nelder-Mead', options={'xatol':1e-12,'fatol':1e-14})
            if -r.fun > best[0]: best = (-r.fun, (n1, n2, n3, r.x))
print('(1) max p4/p2^2 =', best[0], ' 19/24 =', 19/24, ' at counts', best[1][:3])
# random check
mx = 0
for _ in range(200000):
    x = rng.normal(size=9) * rng.exponential(size=9)**2; x -= x.mean()
    mx = max(mx, P(x,4)/P(x,2)**2)
print('    random search max:', mx)

# (2) eigenvectors of regular abelian groups of order 8 on points 2..9 (point 1 fixed)
x2 = np.array([-8] + [1]*8, float)
print('(2) near-scalar x2: p2, p4, Q4, f4 =', P(x2,2), P(x2,4), Q4(x2), f4(x2))
for name, orders in [('E = (Z/2)^3', (2,2,2)), ('Z4 x Z2', (4,2)), ('Z8', (8,))]:
    els = list(itertools.product(*[range(o) for o in orders]))
    for k in els:
        if all(ki == 0 for ki in k): continue
        chi = np.array([np.exp(2j*np.pi*sum(ki*ei/oi for ki,ei,oi in zip(k,e,orders))) for e in els])
        x = np.concatenate([[0], chi])
        ordchi = max(o//np.gcd(o, ki) for o, ki in zip(orders, k))
        print('   %-12s char %s (order %d): p2=%6.2f  Q4=%7.2f  Q5=%7.2f  f4=%7.2f' %
              (name, k, ordchi, abs(P(x,2)), abs(Q4(x)), abs(Q5(x)), abs(f4(x))))

# (3) f4 near x2: second-order term in normal directions n (n_1 = 0, sum n = 0)
n = np.concatenate([[0], rng.normal(size=8)]); n[1:] -= n[1:].mean()
for eps in (1e-2, 1e-3):
    print('(3) f4(x2 + eps n) / (eps^2 p2(n)) =', f4(x2 + eps*n)/(eps**2*P(n,2)))

# (4) -f4 > 0 somewhere on V(R) for each signature r (real coords + conjugate pairs)
for r in (1,3,5,7):
    s = (9 - r)//2; hit = 0
    for _ in range(20000):
        re = rng.normal(size=r); cx = rng.normal(size=s) + 1j*rng.normal(size=s)
        x = np.concatenate([re, cx, cx.conj()]); x -= x.mean()
        hit += (P(x,2).real > 0) and (-f4(x).real > 0)
    print('(4) r = %d: share of random points with p2 > 0 and -f4 > 0: %.1f%%' % (r, 100*hit/20000))

# (5) t^9 - 1 and (t^3-1)^3 lie in the fact 5 family U^3 + lam U^2 + V^2
X, a, lam, v3, v0 = sp.symbols('X a lam v3 v0')
eqs = sp.Poly(sp.expand((X+a)**3 + lam*(X+a)**2 + (v3*X+v0)**2 - (X**3 - 1)), X).all_coeffs()
# explicit solution a = lam = v3 = 0, v0 = i:  t^9 - 1 = (t^3)^3 + i^2;  (t^3-1)^3 = U^3 with lam = 0, V = 0
print('(5) residual at a=lam=v3=0, v0=i:', [sp.simplify(e.subs({a:0,lam:0,v3:0,v0:sp.I})) for e in eqs])
