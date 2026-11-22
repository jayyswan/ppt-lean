# Session 64 (S64.5): residue test for totally ramified local algebras.
# If K_p = prod L_j with L_j totally ramified of degree e_j (tame, residue field F_p) and every u in V_K(Q_p)
# has integral leading valuation (S64.5 lemma), the residues (one value per factor, multiplicity e_j, plus
# the 10th value zeta = -sum e_j x_j) must satisfy sum e_j x_j^k + zeta^k = 0 mod p for k = 3, 5, not all zero.
# Usage: python3 resid64.py <e-list, e.g. 5,3,1> <pmax>     prints the primes p <= pmax with NO nonzero solution.
import sys, itertools, cypari
pari = cypari.pari
es = [int(x) for x in sys.argv[1].split(',')]; pmax = int(sys.argv[2])
bad = []
for p in [int(q) for q in pari('primes([7,%d])' % pmax)]:
    found = False
    for v in itertools.product(range(p), repeat=len(es)):
        if not any(v): continue
        if next(x for x in v if x) != 1: continue          # projective normalisation
        z = (-sum(e * x for e, x in zip(es, v))) % p
        if (sum(e * pow(x, 3, p) for e, x in zip(es, v)) + pow(z, 3, p)) % p: continue
        if (sum(e * pow(x, 5, p) for e, x in zip(es, v)) + pow(z, 5, p)) % p: continue
        found = True; break
    if not found: bad.append(p)
print("e =", es, ": primes p in [7,%d] with no nonzero residue solution:" % pmax, bad)
