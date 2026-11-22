# Session 64 (S64.4): Q_p-points of V_K for an arbitrary degree-9 etale Q_p-algebra prod Q_p[x]/(g_j),
# given by monic integer polynomials g_j (power basis; need not be the maximal order). Same certificate as hens64.py.
# Usage: python3 hensram64.py <p> "<g1>;<g2>;..." [samples] [N] [seed]   (g as PARI polynomials in x)
import sys, random, cypari
from ffalg import Alg
pari = cypari.pari
p = int(sys.argv[1]); polys = sys.argv[2].split(';')
samples = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
N = int(sys.argv[4]) if len(sys.argv) > 4 else 16
rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
M = p ** N
gs = [[int(c) for c in pari('Vecrev(%s)' % g)] for g in polys]
assert sum(len(g) - 1 for g in gs) == 9 and all(g[-1] == 1 for g in gs)
A = Alg(gs, M)
def val(x):
    x %= M
    if x == 0: return N
    v = 0
    while x % p == 0: x //= p; v += 1
    return v
for it in range(samples):
    u = [rng.randrange(M) for _ in range(A.n)]
    if all(x % p == 0 for x in u): continue
    f3, f5 = A.F35(u); v3, v5 = val(f3), val(f5)
    if min(v3, v5) < 1: continue
    g3, g5 = A.grad(u)
    m = min(val(g3[i] * g5[j] - g3[j] * g5[i]) for i in range(A.n) for j in range(i + 1, A.n))
    if m < N and min(v3, v5) >= 2 * m + 1 and 2 * m + 1 < N:
        print(p, polys, "CERTIFIED after", it + 1, "samples: m =", m, "v =", (v3, v5)); break
else:
    print(p, polys, ": no certificate in", samples, "samples")
