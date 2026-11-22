# Session 61: exact membership tests mod p for row E3 (general cubic Bezier x graph of S = T_6).
# u in F_p^9 (conjugate coordinates, K split mod p) is good iff there is a cubic X with X nonconstant on u and
# T_6(X(u_i)) interpolated by a cubic in u_i (5 linear functionals annihilating cubics).
# Usage: python3 e3exact.py <kind> <seed> [p]
#   kind: cheb  (control: 9 of the 18 F_p-roots of T_18(t) = c, i.e. X = T_3, Y = c; after a random affine map of t)
#         rand  (random u)
#         HE    (random F_p-point of H_E = {p1 = 0, 25 p3 p7 = 21 p5^2}: the row-E good locus for arbitrary V)
#         L135  (random F_p-point of L_135)
#         HT6   (planted row-E point for S = T_6 itself: X = alpha t^2 + beta; needs 9 F_p-roots, searched)
# Prints Singular's dim / vdim of the x-system (x0..x3, saturation s*l(x) = 1); 'no solution' = GB is {1}.
import sys, random, subprocess
kind, seed = sys.argv[1], int(sys.argv[2])
p = int(sys.argv[3]) if len(sys.argv) > 3 else 32003
random.seed(seed)
def inv(a): return pow(a % p, p - 2, p)
T6c = [-1, 0, 18, 0, -48, 0, 32]   # T_6 coefficients, low to high

def pev(c, x):
    r = 0
    for co in reversed(c): r = (r*x + co) % p
    return r

def cheb_point():
    # p = 1 mod 36 needed for the full splitting; search c with T_18(t) - c split over F_p
    assert (p - 1) % 36 == 0, 'use p = 1 mod 36, e.g. 32041? -> use 30097'
    g = next(g for g in range(2, p) if all(pow(g, (p-1)//q, p) != 1 for q in set(f for f in range(2, 200) if (p-1) % f == 0 and all(f % d for d in range(2, f)))))
    for _ in range(1000):
        z = pow(g, random.randrange(1, p-1), p)
        zeta = pow(g, (p-1)//18, p)
        xs = sorted({((z*pow(zeta, k, p)) + inv(z*pow(zeta, k, p))) * inv(2) % p for k in range(18)})
        if len(xs) == 18:
            pts = random.sample(xs, 9)
            a, b = random.randrange(1, p), random.randrange(p)
            return [(a*t + b) % p for t in pts]          # generator a t + b: X(t) = T_3((t - b)/a)
    raise RuntimeError

def univ_roots(coeffs_fn, deg):
    # roots in F_p of a univariate polynomial given by evaluation (interpolate, then PARI polrootsmod)
    import cypari; pari = cypari.pari
    xs = list(range(deg + 1)); ys = [coeffs_fn(x) for x in xs]
    P = pari(f'Mod(1,{p})*polinterpolate({xs},{ys})')
    return [int(pari.lift(r)) for r in pari(f'polrootsmod(lift({P}),{p})')]

def psum(u, k): return sum(pow(x, k, p) for x in u) % p

def HE_point():
    for _ in range(500):
        base = [random.randrange(p) for _ in range(7)]
        s = sum(base) % p
        def h(x):
            u = base + [x, (-s - x) % p]
            return (25*psum(u, 3)*psum(u, 7) - 21*psum(u, 5)**2) % p
        for x in univ_roots(h, 10):
            u = base + [x, (-s - x) % p]
            if len(set(u)) == 9 and psum(u, 3) and psum(u, 5):
                return u
    raise RuntimeError

def L135_point():
    import cypari; pari = cypari.pari
    for _ in range(400):
        u = [random.randrange(1, p) for _ in range(6)]; s = sum(u)
        P3 = '+'.join(f'{z}^3' for z in u) + f'+X^3+Y^3+(-({s})-X-Y)^3'
        P5 = '+'.join(f'{z}^5' for z in u) + f'+X^5+Y^5+(-({s})-X-Y)^5'
        R = pari(f'polresultant({P3},{P5},Y)')
        for r in pari(f'polrootsmod({R},{p})'):
            xv = int(pari.lift(r))
            g = pari(f'gcd(Mod(1,{p})*subst({P3},X,{xv}), Mod(1,{p})*subst({P5},X,{xv}))')
            if int(pari.poldegree(g)) < 1: continue
            for yr in pari(f'polrootsmod({pari.lift(g)},{p})'):
                yv = int(pari.lift(yr)); full = u + [xv, yv, (-(s + xv + yv)) % p]
                if len(set(full)) == 9 and psum(full, 7): return full
    raise RuntimeError

def HT6_point():
    # 9 F_p-roots of T_6(alpha t^2 + beta) - Y(t): search random (alpha, beta, Y)
    import cypari; pari = cypari.pari
    for _ in range(20000):
        al, be = random.randrange(1, p), random.randrange(p)
        Y = [random.randrange(p) for _ in range(4)]
        P = pari(f'Mod(1,{p})*(subst(polchebyshev(6),x,{al}*x^2+{be}) - ({Y[0]}+{Y[1]}*x+{Y[2]}*x^2+{Y[3]}*x^3))')
        rts = [int(pari.lift(r)) for r in pari(f'polrootsmod(lift({P}),{p})')]
        if len(set(rts)) >= 9:
            return random.sample(sorted(set(rts)), 9)
    raise RuntimeError

def annihilator(u):
    # 5 x 9 matrix N over F_p with N . (u_i^k)_i = 0 for k = 0..3 (divided differences on 5 consecutive points)
    rows = []
    for j in range(5):
        W = list(range(j, j + 5)); row = [0]*9
        for i in W:
            d = 1
            for k in W:
                if k != i: d = d*(u[i] - u[k]) % p
            row[i] = inv(d)
        rows.append(row)
    return rows

u = {'cheb': cheb_point, 'rand': lambda: [random.randrange(p) for _ in range(9)], 'HE': HE_point,
     'L135': L135_point, 'HT6': HT6_point}[kind]()
assert len(set(u)) == 9
N = annihilator(u)
for row in N:
    for k in range(4): assert sum(r*pow(x, k, p) for r, x in zip(row, u)) % p == 0
Xs = [f'(x0+{x}*x1+{x*x % p}*x2+{pow(x,3,p)}*x3)' for x in u]
T6s = lambda X: f'(32*{X}^6-48*{X}^4+18*{X}^2-1)'
eqs = []
for row in N:
    eqs.append('+'.join(f'{c}*{T6s(X)}' for c, X in zip(row, Xs)))
l = [random.randrange(1, p) for _ in range(3)]
eqs.append(f's*({l[0]}*x1+{l[1]}*x2+{l[2]}*x3)-1')
script = f'ring R = {p},(x0,x1,x2,x3,s),dp;\noption(redSB);\nideal I = ' + ',\n'.join(eqs) + ';\nideal G = std(I);\nprint(dim(G)); print(vdim(G));\nif (size(G)==1) {{ if (G[1]==1) {{print(\"no solution\");}} }}\nquit;\n'
out = subprocess.run(['Singular', '-q'], input=script, capture_output=True, text=True, timeout=600).stdout
print(kind, seed, 'u =', u[:3], '... ->', ' '.join(out.split()))
