"""Exhaustive search over F_l for isomorphism correspondences of bidegree
(2,3), (3,2), (3,3) for the engines with d in {8, 9} (F2.md section 5).

An isomorphism correspondence Gamma: F(lam, lam') = 0 over Q, with deg_lam F = a,
deg_lam' F = b, a, b < min(pq, d), must satisfy (Lemma 5.1):
  (N) support of F in {(0,b), (a,0)} u {(i,j): 1 <= i < a, 1 <= j < b}
      (fibres over 0 and over infinity match);
  (S) every root of F(lam*, y) other than y = lam* has even multiplicity, and
      likewise for F(x, lam*)    (odd-order points over lam* match).
Both conditions survive reduction mod l.  At every smooth F_l-point (x, y) of
the reduced curve with x, y not branch values, Frobenius cycle types of
g - x and g - y must agree (l > d, l not dividing pqd).
For each engine and prime we enumerate ALL F over F_l with (N) and (S) and
report those passing the Frobenius test with >= 12 usable points.
"""
import sys
from itertools import product
sys.path.insert(0, ".")
from flint import nmod_poly

def types_table(p, q, l):
    lam_star = pow(p, p, l) * pow(q, q, l) * pow(pow(p + q, p + q, l), -1, l) % l
    T = {}
    base = [0] * (p + q + 1)
    # g(x) = x^p (1-x)^q as a polynomial mod l
    g = nmod_poly([1], l)
    for _ in range(q):
        g = g * nmod_poly([1, l - 1], l)
    g = g * nmod_poly([0] * p + [1], l)
    for lam in range(l):
        if lam == 0 or lam == lam_star:
            continue
        f = g - lam
        if f.gcd(f.derivative()).degree() > 0:
            continue
        T[lam] = tuple(sorted(h.degree() for h, e in f.factor()[1]))
    return lam_star, T

def even_except(coeffs, root, l):
    """coeffs low->high of a poly in y over F_l (not identically 0): all roots
    other than `root` have even multiplicity."""
    f = nmod_poly(coeffs, l)
    if f.degree() < 0:
        return False  # identically zero: Gamma contains a line, reducible
    for h, e in f.factor()[1]:
        if h.degree() == 1 and (-int(h.coeffs()[0])) % l == root % l:
            continue
        if e % 2:
            return False
    return True

def evaluate(F, x, y, l):
    return sum(c * pow(x, i, l) * pow(y, j, l) for (i, j), c in F.items()) % l

def frob_test(F, a, b, l, lam_star, T):
    usable = 0
    for x in range(l):
        if x not in T:
            continue
        cs = [sum(c * pow(x, i, l) for (i, jj), c in F.items() if jj == j) % l for j in range(b + 1)]
        f = nmod_poly(cs, l)
        if f.degree() <= 0:
            continue
        for h, e in f.factor()[1]:
            if h.degree() != 1:
                continue
            y = (-int(h.coeffs()[0])) % l
            if y not in T:
                continue
            # smoothness: partial derivatives
            Fx = sum(i * c * pow(x, i - 1, l) * pow(y, j, l) for (i, j), c in F.items() if i) % l
            Fy = sum(j * c * pow(x, i, l) * pow(y, j - 1, l) for (i, j), c in F.items() if j) % l
            if Fx == 0 and Fy == 0:
                continue
            if T[x] != T[y]:
                return False, usable
            usable += 1
    return True, usable

def support(a, b):
    S = [(0, b), (a, 0)] + [(i, j) for i in range(1, a) for j in range(1, b)]
    return S

def _solve_affine(rows, rhs, n, l):
    """All solutions over F_l of rows * v = rhs (n unknowns); None if > l^2."""
    M = [list(r) + [b] for r, b in zip(rows, rhs)]
    piv, r = [], 0
    for c in range(n):
        k = next((i for i in range(r, len(M)) if M[i][c] % l), None)
        if k is None:
            continue
        M[r], M[k] = M[k], M[r]
        inv = pow(M[r][c], -1, l)
        M[r] = [x * inv % l for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % l:
                f = M[i][c]
                M[i] = [(x - f * y) % l for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
    if any(all(x % l == 0 for x in row[:n]) and row[n] % l for row in M):
        return []
    free = [c for c in range(n) if c not in piv]
    if len(free) > 2:
        return None
    sols = []
    for fv in product(range(l), repeat=len(free)):
        v = [0] * n
        for c, x in zip(free, fv):
            v[c] = x
        for i, c in enumerate(piv):
            v[c] = (M[i][n] - sum(M[i][f] * v[f] for f in free)) % l
        sols.append(v)
    return sols

def _shape(deg, h, lam_star, l):
    """Monic (t - lam*)^(deg mod 2) (t - h)^(2 floor(deg/2)), low->high coeffs."""
    f = nmod_poly([1], l)
    if deg % 2:
        f = f * nmod_poly([(-lam_star) % l, 1], l)
    for _ in range(deg // 2):
        f = f * nmod_poly([(-h) % l, 1], l) ** 2
    return [int(c) for c in f.coeffs()]

def enumerate_curves(a, b, l, lam_star):
    """All F over F_l with (N) and (S), c_{0b} = 1, c_{a0} != 0.
    For a, b <= 3, (S) says F(lam*, y) = (y - lam*)^(b mod 2)(y - h)^(2 floor(b/2))
    and F(x, lam*) = c_{a0} (x - lam*)^(a mod 2)(x - h')^(2 floor(a/2)), h, h' in F_l.
    Unknowns: c_{a0} and the interior coefficients; the conditions are linear."""
    assert a <= 3 and b <= 3
    inner = [(i, j) for i in range(1, a) for j in range(1, b)]
    unk = [(a, 0)] + inner
    n = len(unk)
    seen, out = set(), []
    for h in range(l):
        P = _shape(b, h, lam_star, l)
        for h2 in range(l):
            R = _shape(a, h2, lam_star, l)
            rows, rhs = [], []
            # F(lam*, y): coefficient of y^j equals P[j]
            for j in range(b + 1):
                row = [pow(lam_star, i, l) if jj == j else 0 for (i, jj) in unk]
                const = 1 if j == b else 0  # the c_{0b} = 1 term
                rows.append(row); rhs.append((P[j] - const) % l)
            # F(x, lam*) - c_{a0} R(x) = 0: coefficient of x^i
            for i in range(a + 1):
                row = []
                for (ii, j) in unk:
                    v = pow(lam_star, j, l) if ii == i else 0
                    if (ii, j) == (a, 0):
                        v = (v - R[i]) % l
                    row.append(v)
                const = pow(lam_star, b, l) if i == 0 else 0
                rows.append(row); rhs.append((-const) % l)
            sols = _solve_affine(rows, rhs, n, l)
            if sols is None:
                raise RuntimeError("solution space too large")
            for v in sols:
                if v[0] % l == 0:
                    continue
                key = tuple(v)
                if key in seen:
                    continue
                seen.add(key)
                F = {(0, b): 1}
                F.update({s: x for s, x in zip(unk, v) if x})
                out.append(F)
    return out

def is_diagonal_multiple(F, a, b, l):
    """F vanishes identically on the diagonal (Gamma contains Delta)."""
    return all(evaluate(F, t, t, l) == 0 for t in range(min(l, a + b + 2)))

if __name__ == "__main__":
    engines = [(7, 1), (5, 3), (8, 1), (7, 2), (5, 4)]
    primes = [int(x) for x in sys.argv[1:]] or [37, 41]
    for (p, q) in engines:
        for l in primes:
            lam_star, T = types_table(p, q, l)
            for (a, b) in [(2, 3), (3, 2), (3, 3)]:
                cands = enumerate_curves(a, b, l, lam_star)
                passing = []
                for F in cands:
                    if is_diagonal_multiple(F, a, b, l):
                        continue
                    ok, n = frob_test(F, a, b, l, lam_star, T)
                    if ok and n >= 12:
                        passing.append((n, F))
                print("pp(%d,%d) l=%d bideg (%d,%d): %d curves satisfy (N),(S); %d pass Frobenius with >=12 points"
                      % (p, q, l, a, b, len(cands), len(passing)), passing[:3], flush=True)
