"""Session 12: invariants vanishing on the (4,4,1) planes.

For the Klein group V4 = translations of F_8 by W = {0,1,w,1+w} (inside PSL(2,8)), the fixed
plane in V is Pi = {x : x_inf = c, x = a on W, x = b on W + w^2, c = -4(a+b)}.  Pi is also the
plane of (4,4,1) vectors used for D in session 8.  For each degree d we count
  dim of PSL(2,8)-invariants on V, and of those vanishing on Pi (hence on all 63 conjugates),
  dim of S_9-invariants on V, and of those vanishing on Pi.
Ranks are computed mod a large prime at random points (generic rank = rational rank w.h.p.).
"""
import random, itertools
from psl28 import invariant_orbits, eval_mon

P = 2**61 - 1
rnd = random.Random(2026)

def rank_mod(rows):
    rows = [r[:] for r in rows]
    rk, ncol = 0, len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % P), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], P - 2, P)
        rows[rk] = [v * inv % P for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(v - f * w) % P for v, w in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def rand_V():
    x = [rnd.randrange(P) for _ in range(8)]
    return x + [(-sum(x)) % P]

W = [0, 1, 2, 3]; Wc = [4, 5, 6, 7]
def rand_Pi():
    a, b = rnd.randrange(P), rnd.randrange(P)
    x = [0] * 9
    for i in W: x[i] = a
    for i in Wc: x[i] = b
    x[8] = (-4 * (a + b)) % P
    return x

def power_sum_monomials(d):  # S_9 invariants: products of p_k, k>=2 (p_1 = 0 on V)
    def parts(n, m):
        if n == 0: yield (); return
        for k in range(min(n, m), 1, -1):
            for r in parts(n - k, k): yield (k,) + r
    return list(parts(d, 9))

def ev_psum(part, x):
    r = 1
    for k in part: r = r * (sum(pow(v, k, P) for v in x) % P) % P
    return r

def ev_orbit(orb, x):
    return sum(eval_mon(m, x) for m in orb) % P

if __name__ == '__main__':
    import sys
    maxd = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for d in range(2, maxd + 1):
        sym = power_sum_monomials(d)
        nV = len(sym) + 5
        sV = rank_mod([[ev_psum(p, x) for p in sym] for x in [rand_V() for _ in range(nV)]])
        sPi = rank_mod([[ev_psum(p, x) for p in sym] for x in [rand_Pi() for _ in range(d + 6)]])
        orbs = invariant_orbits(d)
        nV = len(orbs) + 5
        gV = rank_mod([[ev_orbit(o, x) for o in orbs] for x in [rand_V() for _ in range(nV)]])
        gPi = rank_mod([[ev_orbit(o, x) for o in orbs] for x in [rand_Pi() for _ in range(d + 6)]])
        print(f"d={d}: S_9 invariants on V {sV}, vanishing on Pi {sV - sPi};  "
              f"PSL(2,8) invariants on V {gV}, vanishing on Pi {gV - gPi}", flush=True)
