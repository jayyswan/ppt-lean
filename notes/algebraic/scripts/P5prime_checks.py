"""P5' arithmetic checks (Python fallback; Wolfram not attached in this session).

1. Trinomial shape locus of a degree-N field: the curve {p1 = ... = p_{N-2} = 0} in P^{N-2}
   (complete intersection of degrees 2..N-2).  Adjunction genus vs the Galois-closure genus of
   the three-point map x^N/(1-x) (P1' 4.2: e0 = N, e_inf = N-1).
2. pp(p,q) shape-locus genus for coprime p,q>0 (P1' 4.2) at small N.
3. Hurwitz count: covers pulled back from a three-point degree-N engine along a degree-m lambda
   versus all simply branched degree-N covers of the same genus.
"""
from fractions import Fraction as Fr
from math import factorial, gcd, prod

def ci_genus(N):
    degs = list(range(2, N - 1))          # p2..p_{N-2}
    n = N - 2                             # ambient P^n
    if not degs:                          # N = 3: P^1, no condition
        return 0
    two_g_minus_2 = prod(degs) * (sum(degs) - n - 1)
    return two_g_minus_2 // 2 + 1

def belyi_genus(N, e0, einf):
    val = Fr(factorial(N)) * (1 - Fr(1, e0) - Fr(1, einf) - Fr(1, 2))
    return val / 2 + 1

print("N  CI-genus  Galois-closure genus (tri)")
for N in range(4, 11):
    print(N, ci_genus(N), belyi_genus(N, N, N - 1))

print("\npp(p,q) coprime, p>q>=1: genus of shape curve")
for N in range(5, 10):
    for q in range(1, N):
        p = N - q
        if p > q and gcd(p, q) == 1:
            print(N, (p, q), belyi_genus(N, p * q, N))

print("\nHurwitz: dim pulled-back (2m+1) vs dim all covers 2m(N-1); codim 2m(N-2)-1")
for N in (5, 9):
    for m in (1, 2, 5, 10):
        G = (m - 1) * (N - 1)
        full = 2 * G - 2 + 2 * N
        assert full == 2 * m * (N - 1)
        print(N, m, "G=", G, "pulled", 2 * m + 1, "all", full, "codim", full - 2 * m - 1)
