"""
R1b step 1: which power laws y = a x^b (a,b rational) have *elliptic* arc length?

Arc length differential:
    ds = sqrt(1 + (a b x^{b-1})^2) dx = sqrt(1 + k x^{2b-2}) dx,   k = a^2 b^2.

Put r = 2b-2 = P/Q in lowest terms (Q>0).  Sub x = u^Q gives
    ds = Q u^{Q-1} sqrt(1 + k u^P) du,
a binomial differential with genus of  y^2 = 1 + k U^P  given by
    g = (P-1)/2  (P odd),   (P-2)/2  (P even).
Chebyshev (m=Q-1, n=P, p=1/2): elementary iff
    (m+1)/P in Z   or   (m+1)/P + 1/2 in Z.
Genus 0 (P=1,2) is always elementary.  Genus 1  <=>  P in {3,4}; elliptic
exactly when that genus-1 integral is non-elementary:
    P=3: elliptic iff 3 does not divide Q      (else Q/3 in Z)
    P=4: elliptic iff Q is odd                 (else Q/4 or Q/4+1/2 in Z)
"""
from fractions import Fraction
from math import gcd

def reduce_frac(num, den):
    g = gcd(abs(num), abs(den))
    return num // g, den // g

def classify(b):
    # r = 2b - 2 = P/Q lowest terms
    r = 2 * b - 2
    P, Q = r.numerator, r.denominator          # Fraction is already reduced, Q>0
    if P == 0:
        return 0, Q, 0, True, None
    # Chebyshev elementarity: m+1 = Q, n = P (may be negative)
    m1_over_P = Fraction(Q, P)
    elem = (m1_over_P.denominator == 1) or ((m1_over_P + Fraction(1, 2)).denominator == 1)
    # genus of y^2 = 1 + k u^P  uses |P|
    Pa = abs(P)
    if Pa % 2 == 1:
        g = (Pa - 1) // 2
    else:
        g = (Pa - 2) // 2
    return P, Q, g, elem, None

rows = []
N = 12
for num in range(-N, N + 1):
    for den in range(1, N + 1):
        b = Fraction(num, den)
        if b == 0:
            continue
        P, Q, g, elem, note = classify(b)
        rows.append((b, P, Q, g, elem, note))

print("=== rational b with |num|,den <= 12, grouped by genus of y^2=1+k u^P ===")
for g in (0, 1, 2):
    sel = sorted({b for (b, P, Q, gg, e, n) in rows if gg == g})
    print(f"genus {g}: {len(sel)} values")
    if g == 1:
        print("   ", sel)
print()
print("=== genus-1 candidates: elementary vs elliptic ===")
for (b, P, Q, g, elem, note) in sorted(rows, key=lambda r: r[0]):
    if g == 1:
        print(f"  b={str(b):>7}  r=2b-2={str(2*b-2):>7}  P={P} Q={Q}  "
              f"{'ELEMENTARY' if elem else 'ELLIPTIC'}")
print()
print("=== ALL elliptic b (genus1, non-elementary) ===")
ell = [b for (b, P, Q, g, e, n) in rows if g == 1 and not e]
for b in sorted(set(ell)):
    print("  b =", b)
print("count distinct:", len(set(ell)))
