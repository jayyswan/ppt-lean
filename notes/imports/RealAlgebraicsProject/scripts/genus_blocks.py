# Genus of Y_m = Xtilde_N / (S_m)^9, N = 9m, where Xtilde_N is the Galois closure (group S_N) of the
# trinomial family x^N + a x + b over the line t = a^N / b^(N-1), branched at 3 points with monodromy
# an N-cycle, an (N-1)-cycle (+ fixed point) and a transposition.
# Y_m parametrises trinomial roots tau whose root field contains a fixed degree-9 field K (blocks of size m).
# Points of Y_m -> P^1: ordered partitions of {1..N} into 9 labelled blocks of size m.
from math import factorial, gcd
from functools import lru_cache
from fractions import Fraction
def fix(cycles, m, nb=9):
    # number of assignments of cycles to nb labelled blocks with each block total exactly m
    cycles=tuple(sorted(cycles,reverse=True))
    @lru_cache(None)
    def go(i, fill):
        if i==len(cycles): return 1 if all(f==m for f in fill) else 0
        c=cycles[i]; tot=0
        for b in range(nb):
            if fill[b]+c<=m:
                nf=list(fill); nf[b]+=c; tot+=go(i+1,tuple(nf))
        return tot
    return go(0,(0,)*nb)
def power_cycles(ct, k):
    out=[]
    for c in ct:
        g=gcd(c,k); out+= [c//g]*g
    return out
def orbits(ct, m):
    from math import lcm
    n=1
    for c in ct: n=lcm(n,c)
    return Fraction(sum(fix(power_cycles(ct,k),m) for k in range(n)), n)
for m in [1,2,3]:
    N=9*m; d=factorial(N)//factorial(m)**9
    types=[[N],[N-1,1],[2]+[1]*(N-2)]
    o=[orbits(t,m) for t in types]
    chi=-2*d+sum(d-x for x in o)
    print('m=%d N=%d degree %d  orbits %s  genus %s'%(m,N,d,[int(x) for x in o],(chi+2)/2))
