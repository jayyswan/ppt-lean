# Session 64 (S64.2 check): smooth F_p-points of V_K mod p for unramified types, by random affine plane sections.
# Usage: python3 plane64.py <type, e.g. 7,2> <pmin> <pmax> [seed] [maxplanes]
# For every prime p in [pmin, pmax]: random F_p-plane u = A + sB + tC in the algebra prod F_{p^f};
# F3, F5 restricted (exact multinomial expansion), resultant in t, F_p-roots, common t, gradient rank 2 check.
# Prints primes where no smooth point was found within maxplanes planes (expected: none), and a summary.
import sys, random
from math import comb
import cypari
from ffalg import Alg, irred_mod_p
pari = cypari.pari
lam = [int(x) for x in sys.argv[1].split(',')]
pmin, pmax = int(sys.argv[2]), int(sys.argv[3])
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
maxpl = int(sys.argv[5]) if len(sys.argv) > 5 else 40
rng = random.Random(seed)
s_, t_ = pari('s'), pari('t')

def rank2(g3, g5, p):
    for i in range(len(g3)):
        for j in range(i + 1, len(g3)):
            if (g3[i] * g5[j] - g3[j] * g5[i]) % p: return True
    return False

def try_plane(A, p):
    n = A.n
    V = [[rng.randrange(p) for _ in range(n)] for _ in range(3)]
    E = [A.split(v) for v in V]
    one = [[1] + [0] * (f - 1) for f in A.dims]
    # powers
    pw = [[one] for _ in range(3)]
    for i in range(3):
        for k in range(5): pw[i].append(A.mul(pw[i][-1], E[i]))
    trs = [A.tr(E[i]) for i in range(3)]
    def Fk(k):
        P = pari(0)
        for a in range(k + 1):
            for b in range(k + 1 - a):
                c = k - a - b
                mon = A.mul(A.mul(pw[0][a], pw[1][b]), pw[2][c])
                coef = comb(k, a) * comb(k - a, b)
                P += coef * A.tr(mon) * s_ ** b * t_ ** c
        L = (trs[0] + trs[1] * s_ + trs[2] * t_) ** k
        return (P - L) * pari('Mod(1,%d)' % p)
    F3, F5 = Fk(3), Fk(5)
    R = pari('polresultant')(F3, F5, t_)
    if R == 0: return None
    roots = pari('polrootsmod')(pari('lift')(R), p)
    for s0 in roots:
        s0 = int(pari('lift')(s0))
        f3 = pari('subst')(F3, 's', s0); f5 = pari('subst')(F5, 's', s0)
        G = pari('gcd')(f3, f5)
        if pari('poldegree')(G, 't') < 1: continue
        for t0 in pari('polrootsmod')(pari('lift')(G), p):
            t0 = int(pari('lift')(t0))
            u = [(V[0][i] + s0 * V[1][i] + t0 * V[2][i]) % p for i in range(n)]
            if not any(u): continue
            a3, a5 = A.F35(u)
            assert a3 == 0 and a5 == 0
            g3, g5 = A.grad(u)
            if rank2(g3, g5, p): return u
    return None

primes = [int(q) for q in pari('primes([%d,%d])' % (pmin, pmax))]
fails = []; used = []
for p in primes:
    gs = [irred_mod_p(f, p, rng) for f in lam]
    A = Alg(gs, p)
    ok = False
    for k in range(maxpl):
        if try_plane(A, p) is not None:
            ok = True; used.append(k + 1); break
    if not ok: fails.append(p)
print("type", lam, "primes", len(primes), "in", [pmin, pmax], "no smooth point found at:", fails,
      " max planes used:", max(used) if used else None)
