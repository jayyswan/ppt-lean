"""d = 5 positive control: the commensurator correspondence of Delta(2,4,5).

Delta(4,4,5) has index 6 in Delta(2,4,5) and index 2 in Delta(2,4,10); the
order-2 element of Delta(2,4,10) swapping the two order-4 cone points lies in
the commensurator of Delta(2,4,5).  Concretely:
  lambda1(s) = -(s^2 - 6s + 25)(s - 1)^4 / (3125 s)   (passport [2,2,2],[4,1,1],[5,1])
  alpha(s)   = 25 s / (6 s - 25)                      (fixes s = 0, swaps 3 +- 4i)
  lambda2    = lambda1 o alpha.
Checks (exact, python-flint):
  1. lambda1 - lambda* = -(s^3 - 5s^2 + 15s + 5)^2 / (3125 s), lambda* = 4^4/5^5.
  2. lambda2 != lambda1.
  3. Frobenius cycle types of x^4(1-x) - lambda1(s) and - lambda2(s) agree at every
     s in F_l (l = 7..400, l != 5) where both are etale  -> isomorphic pullbacks.
  4. The cycle types along lambda1 lie in F20 = AGL(1,5): the family is solvable.
"""
import sys
sys.path.insert(0, ".")
from flint import fmpq_poly, fmpq, nmod_poly
from F1_core import primes_between

s = fmpq_poly([0, 1])
G = s * s - 6 * s + 25
num1 = -G * (s - 1) ** 4
den1 = fmpq_poly([0, 3125])
lam_star = fmpq(4 ** 4, 5 ** 5)
Q = fmpq_poly([5, 15, -5, 1])
# 1.
assert num1 - lam_star * den1 == -Q * Q, "lambda* fibre is not [2,2,2]"
print("1. lambda1 - lambda* = -Q^2/(3125 s), Q = s^3-5s^2+15s+5: ok")
# 2. lambda2 = lambda1(alpha(s)), alpha = 25s/(6s-25): clear denominators by (6s-25)^6
a_num, a_den = 25 * s, 6 * s - 25
def compose(coeffs_low_to_high, deg):
    out = fmpq_poly([0])
    for i, c in enumerate(coeffs_low_to_high):
        out += c * a_num ** i * a_den ** (deg - i)
    return out
num2 = compose(num1.coeffs(), 6)
den2 = compose(den1.coeffs(), 6)
assert num1 * den2 != num2 * den1
print("2. lambda2 = lambda1 o alpha differs from lambda1: ok")

F20_TYPES = {(1, 1, 1, 1, 1), (1, 2, 2), (1, 4), (5,)}

def ftype(l, lam):
    """Sorted factor degrees of x^4(1-x) - lam over F_l, or None if not squarefree."""
    f = nmod_poly([(-lam) % l, 0, 0, 0, 1, l - 1], l)
    if f.degree() < 5 or f.gcd(f.derivative()).degree() > 0:
        return None
    return tuple(sorted(g.degree() for g, e in f.factor()[1] for _ in range(e)))

checked, sol_types, bad = 0, set(), []
for l in primes_between(7, 400):
    if l == 5:
        continue
    n1 = [int(c.p) * pow(int(c.q), -1, l) % l for c in num1.coeffs()]
    d1 = [int(c.p) * pow(int(c.q), -1, l) % l for c in den1.coeffs()]
    n2 = [int(c.p) * pow(int(c.q), -1, l) % l for c in num2.coeffs()]
    d2 = [int(c.p) * pow(int(c.q), -1, l) % l for c in den2.coeffs()]
    ev = lambda cs, x: sum(c * pow(x, i, l) for i, c in enumerate(cs)) % l
    for x in range(l):
        D1, D2 = ev(d1, x), ev(d2, x)
        if D1 == 0 or D2 == 0:
            continue
        L1 = ev(n1, x) * pow(D1, -1, l) % l
        L2 = ev(n2, x) * pow(D2, -1, l) % l
        t1, t2 = ftype(l, L1), ftype(l, L2)
        if t1 is None or t2 is None:
            continue
        checked += 1
        sol_types.add(t1)
        if t1 != t2:
            bad.append((l, x, t1, t2))
print("3. points checked: %d, mismatches: %d" % (checked, len(bad)), bad[:5])
print("4. cycle types seen along lambda1:", sorted(sol_types),
      "subset of F20 types:", sol_types <= F20_TYPES)
