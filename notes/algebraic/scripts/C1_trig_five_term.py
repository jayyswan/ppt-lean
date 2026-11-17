"""C1: the five-term sine x sine engine.

A cos(p th) + B sin(p th) + C cos(q th) + D sin(q th) + E = 0, in t = tan(th/2):
G(t) = A Re(1+it)^{2p} + B Im(1+it)^{2p} + (C Re(1+it)^{2q} + D Im(1+it)^{2q})(1+t^2)^{p-q} + E (1+t^2)^p.
Checks: G has 2p distinct real roots (Sturm, exact) and Gal(G/Q) = S_{2p} (Frobenius cycle types).
Backend: python-flint (Python fallback, labelled).
"""
import sys
from fractions import Fraction
from flint import fmpz_poly, fmpq_poly
sys.path.insert(0, ".")
from C1_chebyshev_trinomial import sturm_count, certify_Sn

def re_im(k):
    """(Re, Im) of (1+it)^(2k) as integer polynomials in t"""
    re, im = fmpz_poly([1]), fmpz_poly([0])
    t = fmpz_poly([0, 1])
    for _ in range(2 * k):
        re, im = re - t * im, im + t * re
    return re, im

def G(p, q, A, B, C, D, E, den):
    rp, ip = re_im(p); rq, iq = re_im(q)
    w = fmpz_poly([1, 0, 1])
    return A * rp + B * ip + (C * rq + D * iq) * w ** (p - q) + E * w ** p

for p, q in [(3, 1), (4, 1), (5, 1), (5, 2), (6, 1), (7, 3), (8, 3), (9, 2), (10, 3)]:
    done = False
    for (A, B, C, D, E) in [(21, 0, 2, 5, 3), (21, 0, 5, 2, -3), (35, 12, 3, 4, 5), (40, 9, 7, -3, 2), (60, 11, 5, 9, -7)]:
        F = G(p, q, A, B, C, D, E, 1)
        if F.degree() != 2 * p: continue
        nreal = sturm_count(fmpq_poly(F), Fraction(-10**9), Fraction(10**9))
        cert = certify_Sn(F)
        if nreal == 2 * p and None not in cert:
            print(f"(p,q)=({p},{q}), (A,B,C,D,E)={(A,B,C,D,E)}: degree {2*p}, {nreal} real roots, S_{2*p} certified by primes {cert}")
            done = True; break
    if not done:
        print(f"(p,q)=({p},{q}): no certified example in the list")
