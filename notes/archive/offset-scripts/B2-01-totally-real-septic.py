"""
B2-01: find/verify a totally real irreducible septic over Q and gather Galois
evidence from factorisation cycle types mod primes (no GaloisGroup available).
"""
from sympy import symbols, Poly, factor_list, nroots, Rational, factor
import numpy as np, itertools

x = symbols('x')

def real_root_count(poly_expr):
    p = Poly(poly_expr, x)
    coeffs = [complex(c) for c in reversed(p.all_coeffs())]
    r = np.roots(coeffs)
    return int(np.sum(np.abs(r.imag) < 1e-9)), np.sort(r.real)

def cycle_type_from_factors(poly_expr, q):
    """factor degrees mod q -> cycle type of Frobenius"""
    p = Poly(poly_expr, x)
    try:
        fl = factor_list(p, modulus=q)
    except Exception as e:
        return None
    degs = []
    for f, m in fl[1]:
        degs += [Poly(f, x).degree()] * m
    return sorted(degs, reverse=True)

# base totally real (reducible): x(x^2-1)(x^2-4)(x^2-9) = x^7-14x^5+49x^3-36x
base = x**7 - 14*x**5 + 49*x**3 - 36*x
print("base real roots:", real_root_count(base)[0])

for c in range(1, 60):
    f = base + c
    p = Poly(f, x)
    if not p.is_irreducible:
        continue
    nr, roots = real_root_count(f)
    if nr == 7:
        print("\n*** totally real irreducible septic:  f =", f, " c =", c)
        print("    real roots:", nr)
        print("    nroots:", [complex(r) for r in nroots(f, n=20)])
        print("    factor over Q:", factor(f))
        cycle = {}
        for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47]:
            ct = cycle_type_from_factors(f, q)
            cycle[q] = ct
        for q, ct in cycle.items():
            print(f"      p={q:2d}: {ct}")
        break

# Also: totally real septic with Galois group A7/S7 check via a 7-cycle + others
