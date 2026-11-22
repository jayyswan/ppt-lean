# Session 62: Frobenius cycle types of the degree-90 scheme B5_0 on one INTEGER plane, over many primes.
# Usage: python3 b5frob.py <seed> <nprimes>   (reuses b5deg.py's construction with fixed small integers)
import sys, random, subprocess, re, cypari
import sympy as sp
pari = cypari.pari
seed, npr = int(sys.argv[1]), int(sys.argv[2])
random.seed(seed)
C = [[random.randrange(-9, 10) for _ in range(9)] for _ in range(3)]
x, y, s = sp.symbols('x y s')
U = [C[0][i] + C[1][i]*x + C[2][i]*y for i in range(9)]
Z = [sp.Poly(u + s, x, y, s) for u in U]; zeta = sp.Poly(-sum(U) - 9*s, x, y, s)
q = lambda k: sum((z**k for z in Z), sp.Poly(0, x, y, s)) + zeta**k
q2, q3, q4, q5, q6 = map(q, (2, 3, 4, 5, 6))
eqs = [q3, q5, q2**3 - 15*q2*q4 + 50*q6]
pats = []
for pr in [p for p in range(40009, 60000) if sp.isprime(p)][:npr]:
    fn = f'b5f_{seed}_{pr}.ms'
    txt0 = ',\n'.join(str(sp.Poly(e.as_expr(), x, y, s, domain=sp.GF(pr)).as_expr()).replace('**', '^') for e in eqs) + '\n'  # reduce mod p first: msolve misreads coefficients >= 2^31
    open(fn, 'w').write('x,y,s\n' + str(pr) + '\n' + txt0)
    subprocess.run(['msolve', '-f', fn, '-o', fn + '.out', '-t', '2'], capture_output=True)
    t = open(fn + '.out').read()
    m = re.search(r'\[1,\s*\[\[(\d+),\s*\[([0-9,\s]+)\]', t)
    if not m: print(pr, 'no parametrisation'); continue
    co = [int(c) for c in re.split(r'[,\s]+', m.group(2).strip())]
    f = pari('Pol(' + str(co[::-1]) + ')')
    fa = pari.factormod(f, pr)
    degs = sorted(int(pari.poldegree(g)) for g in fa[0])
    sq = all(int(e) == 1 for e in fa[1])
    pats.append(degs); print(pr, 'deg', m.group(1), 'cycle type', degs, 'squarefree', sq, flush=True)
sums = None
for d in pats:
    ss = {0}
    for a in d: ss |= {v + a for v in ss}
    sums = ss if sums is None else sums & ss
print('common subset sums:', sorted(sums))
