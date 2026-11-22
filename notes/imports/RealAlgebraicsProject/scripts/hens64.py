# Session 64 (S64.3): Q_p-points of V_K for unramified degree-9 algebras at small p (p = 2, 3, 5, 7), by type.
# Usage: python3 hens64.py <type, e.g. 9 or 5,3,1> <p> [samples] [N] [seed]
# Random u in (Z/p^N)^9 (algebra prod Z_{p^f}, f the parts of the type); certificate: a 2x2 minor of the
# gradient matrix of (F3, F5) with valuation m and v(F3), v(F5) >= 2m+1  =>  a smooth Q_p-point nearby
# (multivariate Hensel / p-adic Newton-Kantorovich). Prints the first certificate found (u, m, valuations).
import sys, random
from ffalg import Alg, irred_mod_p
lam = [int(x) for x in sys.argv[1].split(',')]
p = int(sys.argv[2])
samples = int(sys.argv[3]) if len(sys.argv) > 3 else 200000
N = int(sys.argv[4]) if len(sys.argv) > 4 else 14
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
rng = random.Random(seed)
M = p ** N
gs = [irred_mod_p(f, p, rng) for f in lam]   # lifts of irreducible polynomials mod p: unramified Z_{p^f}
A = Alg(gs, M)

def val(x):
    x %= M
    if x == 0: return N
    v = 0
    while x % p == 0: x //= p; v += 1
    return v

best = None
for it in range(samples):
    u = [rng.randrange(M) for _ in range(A.n)]
    if all(x % p == 0 for x in u): continue
    f3, f5 = A.F35(u)
    v3, v5 = val(f3), val(f5)
    if min(v3, v5) < 1: continue
    g3, g5 = A.grad(u)
    m = N
    for i in range(A.n):
        for j in range(i + 1, A.n):
            m = min(m, val(g3[i] * g5[j] - g3[j] * g5[i]))
    if m < N and min(v3, v5) >= 2 * m + 1 and 2 * m + 1 < N:
        print("type", lam, "p", p, "CERTIFIED after", it + 1, "samples: m =", m, " v(F3), v(F5) =", (v3, v5))
        print("  g =", gs, " u =", u)
        break
else:
    print("type", lam, "p", p, ": no certificate in", samples, "samples")
