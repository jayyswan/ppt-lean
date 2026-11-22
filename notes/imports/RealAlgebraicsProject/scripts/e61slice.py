# Session 61: exact count mod p of the T_6 fibre of the shape map J on a 3-space slice of H_E.
# Usage: python3 e61slice.py <seed> <tan|gen|curve> [p] [j4num/j4den]
#   tan  : slice tau0 + span(v1,v2,v3), tau0 an F_p-point of L_135, v_i tangent to H_E there
#          (sum v = 0, sum tau0^2 v = 0)  -- the tangent-residual surface of S60.3/S60.4
#   gen  : generic centred affine 3-space (control)
#   curve: as tan, but only H_E and E6 (I3 = 0): must be positive-dimensional (msolve fails / Singular dim 1)
# Unknowns x1,x2,x3 and y with y*a3 = 1 (saturation: a3 = 0 is where the construction degenerates).
# Writes e61_<seed>_<mode>.ms (msolve input) and runs msolve; prints the number of solutions.
import sys, pickle, subprocess, random
import sympy as sp

seed = int(sys.argv[1]); mode = sys.argv[2]
p = int(sys.argv[3]) if len(sys.argv) > 3 else 32003
j4 = sp.Rational(sys.argv[4]) if len(sys.argv) > 4 else sp.Rational(3, 2)
random.seed(seed)
Gn, E6, E8 = pickle.load(open('e61_formulas.pkl', 'rb'))
a = sp.symbols('a1:10')
cen = {a[0]: 0}
Gc = sp.expand(Gn.subs(cen)); E6c = sp.expand(E6.subs(cen))
if j4 != sp.Rational(3, 2):
    # general I4 = j4 with I3 = 0: m4 = j4 m2^2  <=>  4 B4 = (2 - 2 j4/3) B2^2 ; rebuild E8 from b's
    raise SystemExit('only j4 = 3/2 implemented here')
E8c = sp.expand(E8.subs(cen))

F = sp.GF(p)
def inv(x): return pow(x % p, p - 2, p)

def l135_point():
    # random u1..u6, u9 = -(s + u7 + u8); solve p3 = p5 = 0 for (u7, u8) over F_p via a resultant
    import cypari
    pari = cypari.pari
    for attempt in range(400):
        u = [random.randrange(1, p) for _ in range(6)]
        s = sum(u)
        P3 = '+'.join(f'{z}^3' for z in u) + f'+X^3+Y^3+(-({s})-X-Y)^3'
        P5 = '+'.join(f'{z}^5' for z in u) + f'+X^5+Y^5+(-({s})-X-Y)^5'
        R = pari(f'polresultant({P3},{P5},Y)')
        for r in pari(f'polrootsmod({R},{p})'):
            xv = int(pari.lift(r))
            g = pari(f'gcd(Mod(1,{p})*subst({P3},X,{xv}), Mod(1,{p})*subst({P5},X,{xv}))')
            # P3 is quadratic in Y and symmetric under Y <-> -(s+X+Y), so the gcd has degree 2
            for yr in (pari(f'polrootsmod({pari.lift(g)},{p})') if int(pari.poldegree(g)) >= 1 else []):
                yv = int(pari.lift(yr))
                full = u + [xv, yv, (-(s + xv + yv)) % p]
                if len(set(full)) == 9:
                    p7 = sum(pow(z, 7, p) for z in full) % p
                    if p7 and all(sum(pow(z, k, p) for z in full) % p == 0 for k in (1, 3, 5)):
                        return full
    raise RuntimeError('no L135 point')

def nullspace_mod(rows, n):
    # basis of {v in F_p^n : rows . v = 0}
    M = [r[:] for r in rows]; piv = []; r = 0
    for col in range(n):
        pr = next((i for i in range(r, len(M)) if M[i][col] % p), None)
        if pr is None: continue
        M[r], M[pr] = M[pr], M[r]
        iv = inv(M[r][col]); M[r] = [x*iv % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][col] % p:
                f = M[i][col]; M[i] = [(x - f*y) % p for x, y in zip(M[i], M[r])]
        piv.append(col); r += 1
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        v = [0]*n; v[fc] = 1
        for i, pc in enumerate(piv): v[pc] = (-M[i][fc]) % p
        basis.append(v)
    return basis

xs = sp.symbols('x1 x2 x3'); ysym = sp.Symbol('y')
if mode in ('tan', 'curve'):
    tau0 = l135_point()
    rows = [[1]*9, [z*z % p for z in tau0]]
else:
    tau0 = [random.randrange(p) for _ in range(9)]
    m = sum(tau0) % p; tau0 = [(z - m*inv(9)) % p for z in tau0]
    rows = [[1]*9]
B = nullspace_mod(rows, 9)
V = []
for _ in range(3):
    co = [random.randrange(p) for _ in B]
    V.append([sum(c*b[i] for c, b in zip(co, B)) % p for i in range(9)])
U = [sp.Poly(tau0[i] + sum(V[j][i]*xs[j] for j in range(3)), *xs, domain=F) for i in range(9)]
# power sums and elementary symmetric functions (Newton) -> a_k = (-1)^k e_k
P = [None] + [None]*8
Upow = [u for u in U]
for k in range(1, 9):
    P[k] = sum(Upow, sp.Poly(0, *xs, domain=F))
    if k < 8: Upow = [up*u for up, u in zip(Upow, U)]
E = [sp.Poly(1, *xs, domain=F)]
for k in range(1, 9):
    s = sp.Poly(0, *xs, domain=F)
    for i in range(1, k + 1):
        term = E[k - i]*P[i]
        s = s + term if i % 2 == 1 else s - term
    E.append(s * inv(k))
A = {a[k-1]: E[k]*(1 if k % 2 == 0 else -1) for k in range(1, 9)}
print('a1 identically 0:', A[a[0]].is_zero)

def ev(expr):
    # evaluate a polynomial expression in a2..a8 on the Poly substitutes
    pe = sp.Poly(expr, *a[1:8])
    tot = sp.Poly(0, *xs, domain=F)
    cache = {}
    for mon, co in pe.terms():
        t = sp.Poly(int(sp.Rational(co).p * inv(int(sp.Rational(co).q))) % p, *xs, domain=F)
        for idx, e in enumerate(mon):
            if e:
                key = (idx, e)
                if key not in cache: cache[key] = A[a[idx+1]]**e
                t = t*cache[key]
        tot = tot + t
    return tot

polys = [ev(Gc)]
polys.append(ev(E6c))
if mode != 'curve': polys.append(ev(E8c))
a3p = A[a[2]]
print('degrees:', [q.total_degree() for q in polys], ' a3 degree', a3p.total_degree())
gens = list(xs) + [ysym]
eqs = [q.as_expr() for q in polys] + [sp.expand(ysym*a3p.as_expr() - 1)]
fn = f'e61_{seed}_{mode}.ms'
with open(fn, 'w') as fh:
    fh.write(','.join(map(str, gens)) + '\n' + str(p) + '\n')
    fh.write(',\n'.join(str(sp.expand(e)).replace('**', '^') for e in eqs) + '\n')
print('wrote', fn)
if mode != 'curve':
    out = subprocess.run(['msolve', '-f', fn, '-o', fn + '.out', '-t', '2'], capture_output=True, text=True)
    txt = open(fn + '.out').read()
    # msolve over F_p prints [dim, [char, nvars, deg, vars, linear form, [elim, ...]]]
    print(txt[:300])
