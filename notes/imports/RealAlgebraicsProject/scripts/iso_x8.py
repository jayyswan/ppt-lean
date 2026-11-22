# Session 15. Needs psl_group.py (written from psl_x8.py) next to it.
# Session 15: along the isotropic V4-eigencurves x8 + t e, e = e_chi + i e'_chi, every symmetric
# invariant is a polynomial in t^4 (the entries of e are {1,-1,1,-1,i,-i,i,-i}, stable under x i).
# Find PSL(2,8)-invariants f of degree d with f(x8 + t e) = c t^6 + O(t^8), c != 0, for all three chi.
# usage: python3 iso_x8.py d
import sys, itertools, collections
import sympy as sp
exec(open('psl_group.py').read())   # G, orbit
d = int(sys.argv[1])
def monomials(d, n=9):
    for c in itertools.combinations_with_replacement(range(n), d):
        yield tuple(sorted(collections.Counter(c).items()))
seen, orbs = set(), []
for m in monomials(d):
    if m in seen: continue
    o = sorted({tuple(sorted((g[i], e) for i, e in m)) for g in G}); seen |= set(o); orbs.append(o)
print('degree', d, 'orbits', len(orbs))
def chi(al, v): return (-1) ** bin(al & v).count('1')
t = sp.symbols('t')
def series(orb, x):
    # x: list of 9 polynomials in t as dicts power->Gaussian complex
    tot = collections.defaultdict(complex)
    for m in orb:
        p = {0: 1 + 0j}
        for i, e in m:
            for _ in range(e):
                q = collections.defaultdict(complex)
                for a1, c1 in p.items():
                    for a2, c2 in x[i].items(): q[a1 + a2] += c1 * c2
                p = q
        for k, v in p.items(): tot[k] += v
    return tot
rows = {}   # (chi, power) -> list over orbits
for al in (1, 2, 3):
    x = []
    for j in range(9):
        if j < 4: x.append({0: 1, 1: chi(al, j)})
        elif j < 8: x.append({0: 1, 1: 1j * chi(al, j - 4)})
        else: x.append({0: -8})
    S = [series(o, x) for o in orbs]
    for k in range(0, d + 1):
        rows[(al, k)] = [complex(round(s.get(k, 0).real), round(s.get(k, 0).imag)) for s in S]
# the t^2 coefficient: check it is a multiple of the t^0 one (should be 0 on V for every invariant)
cond = []
for al in (1, 2, 3):
    for k in (0, 2, 4):
        cond.append([sp.Integer(int(z.real)) for z in rows[(al, k)]])
        cond.append([sp.Integer(int(z.imag)) for z in rows[(al, k)]])
M = sp.Matrix(cond)
ker = M.nullspace()
print('kernel dim (t^0,t^2,t^4 = 0 at all three chi):', len(ker))
# image of the kernel in the t^6 coefficients
T6 = []
for al in (1, 2, 3):
    T6.append([sp.Integer(int(z.real)) for z in rows[(al, 6)]]); T6.append([sp.Integer(int(z.imag)) for z in rows[(al, 6)]])
T6 = sp.Matrix(T6)
img = [T6 * v for v in ker]
print('t^6 coefficients of kernel vectors (Re,Im per chi):')
for v in img: print('  ', list(v))
# also t^2 coefficients overall, for information
for al in (1, 2, 3):
    nz = sum(1 for z in rows[(al, 2)] if z != 0)
    print('chi', al, 'orbit sums with nonzero t^2 coeff:', nz, ' t^6:', sum(1 for z in rows[(al, 6)] if z != 0))
import pickle; pickle.dump((orbs, rows, ker), open('iso_x8_%d.pkl' % d, 'wb'))
