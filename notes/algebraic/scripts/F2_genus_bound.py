"""Genus bound behind Proposition 3.1 of F2.md (reduction to isomorphism type).

Let Y be a curve in W_2 over a curve Gamma in P^1 x P^1 whose two pullbacks
lambda_1^* g, lambda_2^* g are NOT isomorphic, with monodromy groups containing
A_d.  Then (F2.md section 3)
  2g(Y) - 2 >= N * k * chi'/2 - (correction),  N >= d!/2,
  correction <= k * [ I(d) + sum_b max_{e1,e2} c_b(e1,e2)/e1 + 2 max c_mix/e0 ],
where chi' = 1/2 - 1/(pq) - 1/d, k = max deg lambda_i, I(d) = #{s : s^2 = 1},
and c(e1,e2) = (1/o) sum_{j=1}^{o-1} [u1^j ~ u2^j != 1] |C(u1^j)| with u_i the
local monodromies (u1 = u_b^e1, u2 = u_b'^e2), o = lcm of their orders.
So g(Y) >= 2 as soon as  d! chi'/4 > I + sum_b ... + 2 ... .
Exact rational arithmetic."""
from fractions import Fraction as Fr
from math import factorial, gcd, lcm
from collections import Counter

def cycle_type(perm):
    n, seen, ct = len(perm), [False] * len(perm), []
    for i in range(n):
        if not seen[i]:
            l, j = 0, i
            while not seen[j]:
                seen[j] = True; j = perm[j]; l += 1
            ct.append(l)
    return tuple(sorted(ct))

def power(perm, e):
    out = list(range(len(perm)))
    for _ in range(e):
        out = [perm[x] for x in out]
    return out

def centralizer(ct):
    c = 1
    for l, m in Counter(ct).items():
        c *= l ** m * factorial(m)
    return c

def order(ct):
    return lcm(*ct)

def involutions(d):
    a, b = 1, 1  # I(0), I(1)
    for n in range(2, d + 1):
        a, b = b, b + (n - 1) * a
    return b

def engine_elements(p, q):
    d = p + q
    u0 = [(i + 1) % p for i in range(p)] + [p + (i + 1) % q for i in range(q)]
    uinf = [(i + 1) % d for i in range(d)]
    ustar = [1, 0] + list(range(2, d))
    return d, {"0": u0, "inf": uinf, "*": ustar}

def c_value(u1, u2):
    t1, t2 = cycle_type(u1), cycle_type(u2)
    o = lcm(order(t1), order(t2))
    tot = 0
    for j in range(1, o):
        a, b = cycle_type(power(u1, j)), cycle_type(power(u2, j))
        if a == b and any(x > 1 for x in a):
            tot += centralizer(a)
    return Fr(tot, o)

def analyse(p, q):
    d, U = engine_elements(p, q)
    chi = Fr(1, 2) - Fr(1, p * q) - Fr(1, d)
    I = involutions(d)
    diag = Fr(0)
    for b, u in U.items():
        ob = order(cycle_type(u))
        best = Fr(0)
        for e1 in range(1, ob):
            for e2 in range(1, ob):
                best = max(best, c_value(power(u, e1), power(u, e2)) / e1)
        diag += best
    mix = Fr(0)
    o0 = order(cycle_type(U["0"]))
    for e0 in range(1, o0):
        mix = max(mix, c_value(power(U["0"], e0), U["*"]) / e0)
    lhs = Fr(factorial(d)) * chi / 4
    rhs = I + diag + 2 * mix
    return d, chi, I, diag, mix, lhs, rhs

if __name__ == "__main__":
    print("engine    d  chi'      I(d)   diag-corr  mixed-corr  d!chi'/4   total-corr  g(Y)>=2?")
    for p, q in [(4, 1), (3, 2), (5, 1), (6, 1), (5, 2), (4, 3), (7, 1), (5, 3), (8, 1), (7, 2), (5, 4)]:
        d, chi, I, diag, mix, lhs, rhs = analyse(p, q)
        print("pp(%d,%d)  %d  %-8s  %-5d  %-9.1f  %-10.1f  %-9.1f  %-10.1f  %s"
              % (p, q, d, chi, I, float(diag), float(mix), float(lhs), float(rhs),
                 "yes" if lhs > rhs else "NO"))
