# Session 64 (S64.2): unramified types of degree-9 algebras, pair numbers m, and the F_p-points of Sing(V_K mod p).
# V_K = {Tr u^3 = (Tr u)^3, Tr u^5 = (Tr u)^5} in P(K); y = (conjugates of u, -Tr u) in F_pbar^10, p1 = p3 = p5 = 0.
# Singular  <=>  the values y_i^2 take at most 2 distinct values (p >= 7).
# Usage: python3 sing64.py <p list>
# Part 1: all 30 partitions of 9 with m = number of disjoint Frobenius-stable +-pairs (involution lemma needs m >= 2).
# Part 2: for the types with m <= 1, brute force of Sing(F_p) inside the reduced family (every odd orbit constant,
#         2-orbit value v in F_{p^2}); the reduction is justified in the text: a non-constant odd orbit already
#         has >= 3 distinct squares.  Also the 7-variable cubic of the tangent-cone lemma on U7 x Q_p.
import sys, itertools
from collections import Counter

def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0: yield (); return
    for k in range(min(n, mx), 0, -1):
        for r in partitions(n - k, k): yield (k,) + r

def mval(lam):
    c = Counter(lam); m = 0
    for v, k in c.items():
        if v % 2 == 0: m += k * v // 2
        else: m += (k // 2) * v
    return m

parts = list(partitions(9))
print("number of types:", len(parts))
hard = [l for l in parts if mval(l) <= 1]
print("types with m <= 1:", hard, " m:", [mval(l) for l in hard])

def nonres(p):
    for n in range(2, p):
        if pow(n, (p - 1) // 2, p) == p - 1: return n

def sing_count(lam, p):
    # reduced family: odd parts -> constant c_j in F_p, a 2-part -> v = (al, be) in F_p[x]/(x^2-n), conjugate (al,-be)
    n = nonres(p)
    odd = [l for l in lam if l % 2 == 1]; two = [l for l in lam if l == 2]
    assert all(l in (1, 2) or l % 2 == 1 for l in lam)
    nv = len(odd) + 2 * len(two)
    cnt = 0; pts = []
    for vals in itertools.product(range(p), repeat=nv):
        if not any(vals): continue
        # build multiset of (a,b) = a + b*sqrt(n) values with multiplicities
        ys = []
        for j, l in enumerate(odd): ys += [(vals[j], 0)] * l
        for j in range(len(two)):
            al, be = vals[len(odd) + 2 * j], vals[len(odd) + 2 * j + 1]
            ys += [(al, be), (al, (-be) % p)]
        z = (-sum(a for a, b in ys)) % p
        ys.append((z, 0))
        def mul(x, y): return ((x[0] * y[0] + n * x[1] * y[1]) % p, (x[0] * y[1] + x[1] * y[0]) % p)
        def pw(x, k):
            r = (1, 0)
            for _ in range(k): r = mul(r, x)
            return r
        ok = True
        for k in (3, 5):
            s = [0, 0]
            for y in ys:
                q = pw(y, k); s[0] += q[0]; s[1] += q[1]
            if s[0] % p or s[1] % p: ok = False; break
        if not ok: continue
        sq = set(mul(y, y) for y in ys)
        if len(sq) <= 2:
            cnt += 1; pts.append(tuple(vals))
    return cnt // (p - 1), pts

for p in [int(x) for x in sys.argv[1:]]:
    print("p =", p)
    for lam in hard:
        c, pts = sing_count(lam, p)
        # representatives up to scaling
        reps = sorted(set(min(tuple((x * s) % p for x in v) for s in range(1, p)) for v in pts))
        print("  type", lam, " #Sing(F_p) =", c, " reps:", reps[:6])
    # 7-variable cubic of the tangent-cone lemma on U7: z = (c^7, -7c); singular iff all z_i^2 equal
    bad = [c for c in range(1, p) if (49 * c * c - c * c) % p == 0]
    print("  cubic on U7 x Q_p: singular F_p-points in the constant family:", len(bad))
