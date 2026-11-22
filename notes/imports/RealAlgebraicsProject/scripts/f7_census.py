"""Session 43: fact 7 family T_9(x) + a T_q(x) + c, q in {1,2,4,5,7,8}.
(1) real-root census: grid of (a, c) rationals, exact Sturm counts (PARI polsturm) -> set of r.
(2) discriminant in a, c: factorisation, is it const * square?  (geometric monodromy A_9 vs S_9)
(3) a rational member with Frobenius cycle types (S_9 witnesses: a 9-cycle... we print the types).
python3 f7_census.py [N]   (N = grid half-size, default 40; about a minute)"""
import sys, itertools
from cypari import pari
pari.allocatemem(10**9)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
for q in (1, 2, 4, 5, 7, 8):
    F = pari(f'polchebyshev(9) + a*polchebyshev({q}) + c')
    rs = {}
    for i in range(-N, N+1):
        for j in range(-N, N+1):
            av, cv = pari(f'{i}/{N//4 if N>=4 else 1}'), pari(f'{j}/{N//2 if N>=2 else 1}')
            f = pari('subst')(pari('subst')(F, 'a', av), 'c', cv)
            if pari('poldisc')(f) == 0: continue
            r = int(pari('polsturm')(f))
            rs.setdefault(r, (i, j))
    D = pari('poldisc')(F, 'x')
    fa = pari('factor')(D)
    sq = all(int(e) % 2 == 0 for e in fa[1])
    print(f'q={q}: r reached {sorted(rs)} (example grid index {rs})', flush=True)
    print(f'   disc_x = {len(fa[0])} factors, exponents {[int(e) for e in fa[1]]}, '
          f'degrees (a,c) {[(int(pari("poldegree")(g,"a")), int(pari("poldegree")(g,"c"))) for g in fa[0]]}, '
          f'square up to const: {sq}', flush=True)
    # rational member with cycle types
    f = pari('subst')(pari('subst')(F, 'a', pari('3/7')), 'c', pari('2/11'))
    if pari('polisirreducible')(f):
        types = set()
        fz = f * pari('denominator(content(%s))' % f)
        lc, dz = pari('pollead')(fz), pari('poldisc')(fz)
        for p in pari('primes(300)'):
            p = int(p)
            if lc % p == 0 or dz % p == 0: continue
            fac = pari('factormod')(fz, p)
            types.add(tuple(sorted((int(pari('poldegree')(h)) for h in fac[0]), reverse=True)))
        print(f'   member a=3/7, c=2/11: irreducible, cycle types {sorted(types)}', flush=True)
