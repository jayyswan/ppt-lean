"""Takeuchi's arithmeticity criterion for triangle groups (a,b,c), checked
against his published list for (2,3,n), then applied to the engine orbifolds
(2, pq, d) of pp(p,q).  Numerics at 60 digits (mpmath)."""
from math import gcd
from mpmath import mp, cos, pi
mp.dps = 60

def lcm(*xs):
    r = 1
    for x in xs:
        r = r * x // gcd(r, x)
    return r

def takeuchi(a, b, c):
    M = lcm(a, b, c)
    def vals(k):
        xs = [cos(k * pi / e) for e in (a, b, c)]
        gens = [x * x for x in xs] + [xs[0] * xs[1] * xs[2]]
        beta = sum(x * x for x in xs) + 2 * xs[0] * xs[1] * xs[2] - 1
        return gens, beta
    g1, b1 = vals(1)
    assert b1 > 0  # hyperbolic
    for k in range(1, 2 * M):
        if gcd(k, 2 * M) != 1:
            continue
        g, bk = vals(k)
        if all(abs(u - v) < mp.mpf(10) ** -40 for u, v in zip(g, g1)):
            continue  # sigma_k trivial on the invariant trace field
        if bk >= 0:
            return False
    return True

# Takeuchi (1977), cocompact (2,3,n): arithmetic exactly for these n <= 40
known = {7, 8, 9, 10, 11, 12, 14, 16, 18, 24, 30}
for n in range(7, 41):
    assert takeuchi(2, 3, n) == (n in known), n
for t in [(2, 4, 5), (2, 4, 6), (2, 4, 7), (2, 4, 8), (2, 4, 10), (2, 4, 12), (2, 4, 18),
          (2, 5, 5), (2, 5, 6), (2, 5, 8), (2, 5, 10), (2, 5, 20), (2, 5, 30),
          (2, 6, 6), (2, 6, 8), (2, 6, 12), (2, 7, 7), (2, 7, 14), (2, 8, 8), (2, 8, 16),
          (2, 9, 18), (2, 10, 10), (2, 12, 12), (2, 12, 24), (2, 15, 30), (2, 18, 18)]:
    assert takeuchi(*t), t
for t in [(2, 4, 9), (2, 4, 11), (2, 5, 7), (2, 5, 9), (2, 6, 7), (2, 7, 8), (2, 3, 13)]:
    assert not takeuchi(*t), t
print("validation against Takeuchi's list: ok")

for p, q in [(4, 1), (3, 2), (5, 1), (6, 1), (5, 2), (4, 3), (7, 1), (5, 3), (8, 1), (7, 2), (5, 4)]:
    d = p + q
    print("pp(%d,%d)  d=%d  orbifold (2,%d,%d)  arithmetic=%s" % (p, q, d, p * q, d, takeuchi(2, p * q, d)))
