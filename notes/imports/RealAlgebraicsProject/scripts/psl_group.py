# Session 15: PSL(2,8) group helper (G, orbit). Read by exec() in the other session 15 scripts.
import itertools
# ---- PSL(2,8) on P^1(F_8), points 0..7 bit vectors (w^3 = w + 1), 8 = infinity
def fmul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
def finv(a):
    for b in range(1, 8):
        if fmul(a, b) == 1: return b
INF = 8
def mob(a, b, c, d, z):
    if z == INF: return INF if c == 0 else fmul(a, finv(c))
    num = fmul(a, z) ^ b; den = fmul(c, z) ^ d
    return INF if den == 0 else fmul(num, finv(den))
G = sorted({tuple(mob(a, b, c, d, z) for z in range(9))
            for a, b, c, d in itertools.product(range(8), repeat=4) if fmul(a, d) ^ fmul(b, c)})
assert len(G) == 504
def orbit(mon):  # mon: dict index->exp
    m = tuple(sorted(mon.items()))
    return sorted({tuple(sorted((g[i], e) for i, e in m)) for g in G})

