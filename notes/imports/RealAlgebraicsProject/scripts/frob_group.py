"""Session 11: decide whether an irreducible f in Z[L] of degree n has Galois group A_n or S_n,
rigorously, from Frobenius cycle types (Dedekind). If some p gives a cycle type with a cycle of
prime length q, n/2 < q <= n-3, then G is primitive (q > n/2 forces every block to be fixed) and
Jordan's theorem gives G >= A_n. A cycle type with an odd number of even-length cycles is an
odd permutation, so G = S_n.  Usage: python3 frob_group.py file.pol [maxprime]
"""
import sys, collections, cypari
pari = cypari.pari
pari.allocatemem(2*10**9)
f = pari(open(sys.argv[1]).read().strip())
f = f / pari.content(f)
n = int(pari.poldegree(f))
maxp = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
print('degree', n, ' irreducible over Q:', bool(pari.polisirreducible(f)))
lead = pari.pollead(f)
ct = collections.Counter(); jordan = None; odd = None; m1 = m2 = 0; tot = 0
for p in pari.primes(maxp):
    p = int(p)
    if p < 5 or lead % p == 0: continue
    fp = pari.factormod(f, p)
    degs = []
    ok = True
    for g, e in zip(fp[0], fp[1]):
        if int(e) > 1: ok = False; break
        degs.append(int(pari.poldegree(pari.lift(g))))
    if not ok or sum(degs) != n: continue
    tot += 1
    degs.sort(); ct[tuple(degs)] += 1
    fx = degs.count(1); m1 += fx; m2 += fx*fx
    if jordan is None:
        for q in degs:
            if 2*q > n and q <= n-3 and pari.isprime(q): jordan = (p, q, degs); break
    if odd is None and sum(1 for d in degs if d % 2 == 0) % 2 == 1: odd = (p, degs)
print('unramified primes used', tot)
print('mean fixed points %.3f (transitive: 1)   mean fixed^2 %.3f (2-transitive: 2)' % (m1/tot, m2/tot))
print('share of n-cycles %.4f (S_n: %.4f)' % (ct[(n,)]/tot, 1/n))
print('Jordan witness (p, prime cycle q, type):', jordan)
print('odd Frobenius (p, type):', odd)
if jordan and odd: print('=> Galois group is S_%d' % n)
elif jordan: print('=> Galois group contains A_%d' % n)
