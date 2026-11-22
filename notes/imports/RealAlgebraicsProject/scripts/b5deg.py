# Session 62: exact counts mod p for row B5 (Bezier (t^2, cubic) x Q-quintic graph).
# Usage: python3 b5deg.py <line|plane|plane0|l135plane> <seed> [p]
#   line     : degree of H5 = {u : exists s with (u+s, zeta) in L135^(10)} on a random line u0 + k u1
#              (unknowns k, s; zeta = -p1(u) - 9 s; equations q3 = q5 = 0)
#   plane    : the codim-2 good locus B5_{I0} (random I0) on a random plane u0 + x u1 + y u2
#              (unknowns x, y, s; equations q3, q5, 40^3 N2^2 - c N3^3 with c random)
#   plane0   : same with I0 = 0 (equation N2 = 0, the odd-quintic class)
#   l135plane: I = 0 on L135 itself (zeta = s = 0): points of L135 cut by a random 4-space? no:
#              here a random 5-space through 0 in centred K meets L135 in a curve; we count
#              {p3 = p5 = N2 = 0} on a random centred 3-space (control: Bezout 3*5*6 = 90)
# q_k = sum (u_i + s)^k + zeta^k,  N2 = q2^3 - 15 q2 q4 + 50 q6,  N3 = q2^2 - 10 q4.
# Conjugate coordinates over F_p (the degree is geometric). Writes b5_<mode>_<seed>.ms, runs msolve.
import sys, random, subprocess
import sympy as sp
mode, seed = sys.argv[1], int(sys.argv[2])
p = int(sys.argv[3]) if len(sys.argv) > 3 else 32003
random.seed(seed)
R = lambda: random.randrange(1, p)
k, x, y, s = sp.symbols('k x y s')
if mode == 'line':
    gens = [k, s]
    U = [R() + R()*k for _ in range(9)]
elif mode in ('plane', 'plane0'):
    gens = [x, y, s]
    U = [R() + R()*x + R()*y for _ in range(9)]
elif mode == 'l135plane':
    gens = [x, y, k]
    c = [[R() for _ in range(9)] for _ in range(4)]
    for v in c:
        m = sum(v) % p; inv9 = pow(9, p - 2, p); v[:] = [(z - m*inv9) % p for z in v]
    U = [c[0][i] + c[1][i]*x + c[2][i]*y + c[3][i]*k for i in range(9)]
F = sp.GF(p)
def P(e): return sp.Poly(e, *gens, domain=F)
if mode == 'l135plane':
    Z = [P(u) for u in U]
    zeta = None
else:
    Z = [P(u + s) for u in U]
    zeta = P(-sum(U) - 9*s)
def q(kk):
    t = sum((z**kk for z in Z), P(0))
    if zeta is not None: t = t + zeta**kk
    return t
q2, q3, q4, q5, q6 = q(2), q(3), q(4), q(5), q(6)
N2 = q2**3 - 15*q2*q4 + 50*q6
N3 = q2**2 - 10*q4
eqs = [q3, q5]
if mode == 'plane': eqs.append(64000*N2**2 - R()*N3**3)
if mode in ('plane0', 'l135plane'): eqs.append(N2)
print(mode, 'degrees', [e.total_degree() for e in eqs])
fn = f'b5_{mode}_{seed}.ms'
with open(fn, 'w') as fh:
    fh.write(','.join(map(str, gens)) + '\n' + str(p) + '\n')
    fh.write(',\n'.join(str(e.as_expr()).replace('**', '^') for e in eqs) + '\n')
out = subprocess.run(['msolve', '-f', fn, '-o', fn + '.out', '-t', '2'], capture_output=True, text=True)
txt = open(fn + '.out').read()
print(txt[:160].replace('\n', ' '))
