"""Unit tests for F1_core (stage A of PLAN-forward-search.md).

Run:  python3 F1_test_core.py        (Windows: py -3 F1_test_core.py)

Positive controls come from engines whose Galois closure C^ has genus 0
(pp(2,1), pp(3,1), tri(4)), where solutions exist at small height.  Every
certified K is re-checked by an independent exact test (Trager norm: K has a
root in B_h = Q[x]/N_h).  The degree-5 positive control is stage B.
"""

import itertools
import sys
import time
from math import gcd

sys.path.insert(0, ".")
from F1_core import (TableCache, certify, cycle_table, fields_isomorphic,  # noqa: E402
                     filter_h, fmpq, fmpz_poly, galois_certificate,
                     has_root_in, nmod_poly, N_of, pp, signature, tri, X)

FAILS = []


def check(name, cond, info=""):
    print(("ok   " if cond else "FAIL ") + name + ("" if cond else "  " + str(info)))
    if not cond:
        FAILS.append(name)


def irreducible_of_degree(h, m):
    f = fmpz_poly(h).factor()[1]
    return len(f) == 1 and f[0][1] == 1 and f[0][0].degree() == m


def primitive(h):
    g = 0
    for v in h:
        g = gcd(g, v)
    return g == 1


def box(m, H):
    for co in itertools.product(range(-H, H + 1), repeat=m):
        for a in range(1, H + 1):
            h = list(co) + [a]
            if h[0] != 0 and primitive(h) and irreducible_of_degree(h, m):
                yield h


# --- cycle tables ------------------------------------------------------------

def test_cycle_table():
    for eng in (pp(3, 2), tri(5), pp(4, 3)):
        for l in (11, 13, 101):
            tab = cycle_table(eng, l)
            ok = True
            for lam in range(l):
                F = nmod_poly([int(c) % l for c in eng.fibre(lam).coeffs()], l)
                sqf = F.degree() == eng.d and F.gcd(F.derivative()).degree() == 0
                if tab[lam] is None:
                    continue
                if not sqf or sum(tab[lam]) != eng.d:
                    ok = False
                direct = tuple(sorted(g.degree() * e for g, e in F.factor()[1]))
                if direct != tab[lam]:
                    ok = False
            check("cycle_table %s mod %d" % (eng, l), ok)


def test_branch_values():
    for eng in (pp(2, 1), pp(3, 2), pp(4, 3), tri(5), tri(6)):
        ok = True
        for b in eng.branch:
            F = eng.fibre(b.numerator, b.denominator)
            if F.discriminant() != 0:
                ok = False
        # a non-branch value has a squarefree fibre
        F = eng.fibre(7, 3)
        ok = ok and F.discriminant() != 0
        check("branch values of %s have singular fibres" % eng, ok)


# --- Mobius relation tri(D) ~ pp(D-1, 1) --------------------------------------

def test_tri_pp_mobius():
    # pp(D-1,1)(1/x) = (1/x)^(D-1) (1 - 1/x) = (x - 1)/x^D  and  tri(D)(x) = x^D/(1 - x).
    # Their product is -1: check num1*num2 == -den1*den2 as polynomials, where
    # (num1, den1) = (x - 1, x^D) is pp(D-1,1)(1/x) obtained by clearing x^D.
    for D in range(3, 10):
        e = pp(D - 1, 1)
        # x^D * e.A(1/x) as a polynomial: reverse the coefficient list of e.A
        co = [int(c) for c in e.A.coeffs()] + [0] * (D + 1 - e.A.length())
        num1, den1 = fmpz_poly(list(reversed(co))), X**D
        t = tri(D)
        ok = num1 == X - 1 and num1 * t.A == -(den1 * t.B)
        check("pp(%d,1)(1/x) * tri(%d)(x) = -1" % (D - 1, D), ok)
    # the certified d = 4 solutions correspond under lam -> -1/lam
    a = certify([5, -30, 32], pp(3, 1))
    b = certify([32, 30, 5], tri(4))       # T^2 h(-1/T), primitive
    check("Mobius pair certified on both sides",
          a.status == "solution" and b.status == "solution" and fields_isomorphic(a.K, b.K),
          (a, b))


# --- positive controls -------------------------------------------------------

def run_box(eng, m, H, use_filter):
    cache = TableCache(eng)
    sols, rejected_solutions, statuses = [], 0, {}
    for h in box(m, H):
        fv = filter_h(h, eng, cache=cache)
        if use_filter and fv[0] == "reject":
            continue
        r = certify(h, eng)
        statuses[r.status] = statuses.get(r.status, 0) + 1
        if r.status == "solution":
            sols.append((h, r.K))
            if fv[0] == "reject":
                rejected_solutions += 1
    return sols, rejected_solutions, statuses


def test_positive(eng, m, H, minimum):
    t = time.time()
    sols, _, st = run_box(eng, m, H, use_filter=True)
    check("%s m=%d H=%d: >= %d certified solutions (got %d, %s, %.1fs)"
          % (eng, m, H, minimum, len(sols), st, time.time() - t), len(sols) >= minimum)
    ok = all(has_root_in(K, N_of(h, eng)) for h, K in sols)
    check("%s m=%d: every certified K has a root in B_h (Trager)" % (eng, m), ok)
    ok = all(K.degree() == eng.d for h, K in sols)
    check("%s m=%d: every K has degree d" % (eng, m), ok)


def test_filter_soundness(eng, m, H):
    """Unfiltered exhaustive box: no certified solution is rejected by filter."""
    t = time.time()
    sols, bad, st = run_box(eng, m, H, use_filter=False)
    check("filter never rejects a certified solution: %s m=%d H=%d (%s, %.1fs)"
          % (eng, m, H, st, time.time() - t), bad == 0)


def test_negative():
    # generic quadratics for tri(5): exact 'none'
    for h in ([1, 1, 3], [-7, 3, 5], [2, -3, 11]):
        r = certify(h, tri(5))
        check("tri(5) h=%s certified 'none'" % h, r.status == "none", r)


# --- Galois groups, isomorphism, signature -----------------------------------

def test_galois_and_iso():
    cases = [([-1, -1, 0, 0, 0, 1], "S5"),          # x^5 - x - 1
             ([16, 20, 0, 0, 0, 1], "A5"),          # x^5 + 20x + 16
             ([1, -3, 0, 1], "A3"),                 # x^3 - 3x + 1
             ([-2, 0, 0, 1], "S3")]
    for co, g in cases:
        got = galois_certificate(fmpz_poly(co))
        check("galois %s -> %s" % (fmpz_poly(co), g), got == (g, "proved"), got)
    got = galois_certificate(fmpz_poly([1, 0, 0, 0, 1]))
    check("galois x^4+1 not claimed S4/A4", got[0] == "?", got)
    check("Q(2^(1/3)) = Q(16^(1/3))", fields_isomorphic(fmpz_poly([-2, 0, 0, 1]), fmpz_poly([-16, 0, 0, 1])))
    check("Q(2^(1/3)) != Q(3^(1/3))", not fields_isomorphic(fmpz_poly([-2, 0, 0, 1]), fmpz_poly([-3, 0, 0, 1])))
    check("signature x^5-x-1 = (1,2)", signature(fmpz_poly([-1, -1, 0, 0, 0, 1])) == (1, 2))
    check("signature x^5-5x+1... = (3,1)", signature(fmpz_poly([1, -5, 0, 0, 0, 1])) == (3, 1))
    check("signature T_5 (cos minpoly) totally real",
          signature(fmpz_poly([0, 5, 0, -20, 0, 16])) == (5, 0))


if __name__ == "__main__":
    test_cycle_table()
    test_branch_values()
    test_tri_pp_mobius()
    test_positive(pp(2, 1), 2, 10, 4)
    test_positive(pp(3, 1), 2, 40, 2)
    test_positive(tri(4), 2, 40, 2)
    test_positive(pp(2, 1), 3, 9, 8)
    test_filter_soundness(pp(2, 1), 2, 6)
    test_filter_soundness(pp(3, 1), 2, 5)
    test_filter_soundness(pp(2, 1), 3, 3)
    test_negative()
    test_galois_and_iso()
    print()
    print("FAILED: %s" % FAILS if FAILS else "all tests passed")
    sys.exit(1 if FAILS else 0)
