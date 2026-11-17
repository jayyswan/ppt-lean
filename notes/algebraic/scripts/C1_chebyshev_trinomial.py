"""C1: the Chebyshev trinomial engine  T_p(x) + a*T_q(x) + c  (sine x sine crossing).

Checks, for each degree p in a range, an explicit rational (a, c, q) such that
  (1) f = T_p + a*T_q + c has p distinct real roots, all in (-1, 1)   [Sturm, exact]
  (2) Gal(f/Q) = S_p   [certificate: cycle types of Frobenius at good primes:
        an n-cycle (transitive), an (n-1)-cycle (so 2-transitive),
        and a type with exactly one even cycle of length 2 and all other lengths odd
        (a power is a transposition).  2-transitive + transposition => S_n.]
Backend: python-flint (exact), Python fallback labelled per the plan's rules.
"""
import sys
from fractions import Fraction
from math import gcd
from flint import fmpz_poly, fmpq_poly, nmod_poly, fmpq

def cheb(n):
    a, b = fmpz_poly([1]), fmpz_poly([0, 1])
    if n == 0: return a
    for _ in range(n - 1):
        a, b = b, 2 * fmpz_poly([0, 1]) * b - a
    return b

def sturm_count(f, lo, hi):
    """number of distinct real roots of f (fmpq_poly) in (lo, hi]"""
    seq = [f, f.derivative()]
    while seq[-1].degree() > 0:
        r = seq[-2] % seq[-1]
        if r.degree() < 0: break
        seq.append(-r)
    def sc(x):
        vals = [s(fmpq(x.numerator, x.denominator)) for s in seq]
        vals = [v for v in vals if v != 0]
        return sum(1 for u, v in zip(vals, vals[1:]) if (u > 0) != (v > 0))
    return sc(lo) - sc(hi)

def cycle_types(F, primes):
    out = {}
    lead = int(F[F.degree()])
    for p in primes:
        if lead % p == 0: continue
        g = nmod_poly([int(c) % p for c in F.coeffs()], p)
        fac = g.factor()[1]
        if any(e > 1 for _, e in fac): continue
        out[p] = tuple(sorted(h.degree() for h, _ in fac))
    return out

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b"\0\0"
    for i in range(2, int(N ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

PR = primes_upto(4000)

def certify_Sn(F):
    n = F.degree()
    ct = cycle_types(F, PR)
    ncyc = next((p for p, t in ct.items() if t == (n,)), None)
    n1 = next((p for p, t in ct.items() if t == (1, n - 1)), None)
    tr = next((p for p, t in ct.items()
               if t.count(2) == 1 and all(l % 2 == 1 for l in t if l != 2)), None)
    return ncyc, n1, tr

def try_params(p, q, a, c):
    den = a.denominator * c.denominator
    F = cheb(p) * den + cheb(q) * (a.numerator * (den // a.denominator)) + fmpz_poly([c.numerator * (den // c.denominator)])
    fq = fmpq_poly(F)
    if sturm_count(fq, Fraction(-1), Fraction(1)) != p: return None
    if F(1) == 0 or F(-1) == 0: return None
    cert = certify_Sn(F)
    if None in cert: return None
    return F, cert

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for p in range(lo, hi + 1):
        found = None
        for q in range(1, p):
            if gcd(p, q) != 1: continue
            for a in (Fraction(1, 3), Fraction(1, 5), Fraction(2, 7), Fraction(-1, 3), Fraction(3, 11), Fraction(1, 7)):
                for c in (Fraction(1, 7), Fraction(1, 11), Fraction(-1, 5), Fraction(2, 13), Fraction(1, 3), Fraction(3, 17)):
                    r = try_params(p, q, a, c)
                    if r: found = (q, a, c, r); break
                if found: break
            if found: break
        if found:
            q, a, c, (F, cert) = found
            print(f"p={p}: T_{p} + ({a}) T_{q} + ({c}):  {p} real roots in (-1,1);  S_{p} certified by primes "
                  f"(n-cycle, (n-1)-cycle, transposition) = {cert}")
        else:
            print(f"p={p}: no certified example in the search box")
