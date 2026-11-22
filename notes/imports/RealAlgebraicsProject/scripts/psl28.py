"""Session 11: PSL(2,8) acting on P^1(F_8) = {0..7, inf}. Builds the group, Molien series for
invariants and for V-covariants on V = trace-zero part of Q^9, compared with S_9, and orbit-sum
bases of invariants / covariants by degree. Imported by later scripts.
Points: 0..7 are elements of F_8 = F_2[w]/(w^3 + w + 1) as bit vectors, 8 = infinity.
"""
import itertools, collections
from fractions import Fraction
import sympy as sp

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

def group():
    G = set()
    for a, b, c, d in itertools.product(range(8), repeat=4):
        if fmul(a, d) ^ fmul(b, c): G.add(tuple(mob(a, b, c, d, z) for z in range(9)))
    return sorted(G)
G = group()
assert len(G) == 504

def cyc(p):
    seen, out = set(), []
    for i in range(9):
        if i in seen: continue
        j, l = i, 0
        while j not in seen: seen.add(j); j = p[j]; l += 1
        out.append(l)
    return tuple(sorted(out))

def molien(maxdeg=12):
    N = maxdeg + 1
    def inv_series(c):  # 1/prod(1 - t^l) * (1 - t), truncated, as Fractions
        s = [Fraction(0)] * N; s[0] = Fraction(1)
        for l in c:
            for k in range(l, N): s[k] += s[k - l]
        return [s[k] - (s[k - 1] if k else 0) for k in range(N)]
    inv = [Fraction(0)] * N; cov = [Fraction(0)] * N
    for p in G:
        c = cyc(p); s = inv_series(c); fix = c.count(1)
        for k in range(N): inv[k] += s[k]; cov[k] += (fix - 1) * s[k]
    s9 = inv_series(tuple(range(1, 10)))
    s9c = [sum(s9[k - j] for j in range(1, 9) if k - j >= 0) for k in range(N)]
    return [int(v / 504) for v in inv], [int(v / 504) for v in cov], [int(v) for v in s9], [int(v) for v in s9c]

def monomials(d, n=9):
    for c in itertools.combinations_with_replacement(range(n), d):
        yield tuple(sorted(collections.Counter(c).items()))

def act(g, m):  # monomial prod x_i^e  ->  prod x_{g(i)}^e
    return tuple(sorted((g[i], e) for i, e in m))

def invariant_orbits(d):
    seen, orbs = set(), []
    for m in monomials(d):
        if m in seen: continue
        o = {act(g, m) for g in G}; seen |= o; orbs.append(sorted(o))
    return orbs

def covariant_orbits(d, p=INF):
    """Orbits of the stabiliser G_p on degree-d monomials; each gives a covariant
    c(x)_{g(p)} = sum over the G_p-orbit of g(m)."""
    Gp = [g for g in G if g[p] == p]
    seen, orbs = set(), []
    for m in monomials(d):
        if m in seen: continue
        o = {act(g, m) for g in Gp}; seen |= o; orbs.append(sorted(o))
    return orbs

def coset_reps(p=INF):
    reps = {}
    for g in G:
        reps.setdefault(g[p], g)
    return [reps[i] for i in range(9)]

def eval_mon(m, x):
    r = 1
    for i, e in m: r *= x[i]**e
    return r

def covariant(orb, x, p=INF):
    """Value at x (list of 9 numbers) of the covariant built from a G_p-orbit of monomials."""
    out = [0] * 9
    for g in coset_reps(p):
        out[g[p]] = sum(eval_mon(act(g, m), x) for m in orb)
    return out

if __name__ == '__main__':
    inv, cov, s9, s9c = molien(10)
    print('degree        ', list(range(11)))
    print('PSL(2,8) inv  ', inv)
    print('S_9 inv       ', s9)
    print('PSL(2,8) cov  ', cov)
    print('S_9 cov       ', s9c)
    for d in range(1, 6):
        print('deg', d, ' G-orbits on monomials', len(invariant_orbits(d)),
              ' G_inf-orbits', len(covariant_orbits(d)))
