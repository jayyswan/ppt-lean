# Real solvability of the quartic resolvent, by signature, and consistency with fact 5.
import pickle, sympy as sp, random, numpy as np
d = pickle.load(open('weier_syms.pkl','rb'))
u,m6,m5,m4,m3,m2,m1,m0,rho,X = sp.symbols('u m6 m5 m4 m3 m2 m1 m0 rho X')
Rc = [sp.lambdify((u,m6,m5,m4,m3,m2,m1,m0), c, 'numpy') for c in sp.Poly(d['R'], rho).all_coeffs()]
gl = [sp.lambdify((u,m6,m5,m4,m3,m2,m1,m0,rho), g, 'numpy') for g in d['g']]
def resolvent_roots(coef):          # coef = monic nonic, numpy poly order, trace zero
    args = (coef[2]/3, coef[3], coef[4], coef[5], coef[6], coef[7], coef[8], coef[9])
    return np.roots([c(*args) for c in Rc]), args
def disc_g(args, r):
    g2,g1,g0 = [g(*args, r) for g in gl]
    return 18*g2*g1*g0 - 4*g2**3*g0 + g2**2*g1**2 - 4*g1**3 - 27*g0**2
rng = np.random.default_rng(1)
print('share of random real nonics (trace zero) whose resolvent has a real root, by number r of real roots:')
for r in (1,3,5,7,9):
    hit = pos = 0; N = 4000
    for _ in range(N):
        re = list(rng.normal(size=r)); cx = [complex(a,b) for a,b in rng.normal(size=((9-r)//2,2))]
        roots = np.array(re + cx + [z.conjugate() for z in cx]); roots = roots - roots.mean()
        coef = np.real(np.poly(roots))
        rr,_ = resolvent_roots(coef)
        real = [z.real for z in rr if abs(z.imag) < 1e-9*max(1,abs(z))]
        hit += len(real) > 0; pos += any(x > 0 for x in real)
    print('  r = %d: real root %.1f%%, positive root %.1f%%' % (r, 100*hit/N, 100*pos/N))
# consistency with fact 5: m = U^3 + lam U^2 + V^2 must show up as a resolvent root with disc(g) = 0
random.seed(2); t = sp.symbols('t')
for trial in range(3):
    uu = sp.Rational(random.randint(-3,3)); u0 = random.randint(-3,3); lam = random.randint(-4,4)
    Vc = [random.randint(-3,3) or 1 for _ in range(4)]
    U = t**3 + uu*t + u0; V = sum(c*t**k for k,c in enumerate(Vc))
    m = sp.Poly(sp.expand(U**3 + lam*U**2 + V**2), t)
    coef = np.array([float(c) for c in m.all_coeffs()])
    rr,args = resolvent_roots(coef)
    best = min(rr, key=lambda z: abs(z - Vc[3]**2))
    print('fact 5 member: v3^2 = %d, nearest resolvent root %.10f, disc(g) there = %.2e, at the other roots: %s'
          % (Vc[3]**2, best.real, abs(disc_g(args,best)), ['%.1e' % abs(disc_g(args,z)) for z in rr if z is not best]))
