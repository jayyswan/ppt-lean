import cypari, random
pari=cypari.pari; pari.allocatemem(10**9)
from collections import Counter
random.seed(int(__import__('sys').argv[1]))
want={1:None,2:None,3:None,4:None,5:None}
tries=0
while any(v is None for v in want.values()) and tries<4000:
    tries+=1
    c=[random.randint(-4,4) for _ in range(10)]
    if c[0]==0: c[0]=1
    f='x^10+'+'+'.join('(%d)*x^%d'%(c[9-k],k) for k in range(10))
    F=pari(f)
    if not pari.polisirreducible(F): continue
    r=int(pari.polsturm(F)); s=(10-r)//2
    if s not in want or want[s] is not None: continue
    has7=False; odd=False
    for p in pari.primes(200)[3:]:
        if pari.poldisc(F)%p==0: continue
        fa=pari.factormod(F,p); degs=[int(pari.poldegree(fa[0][i])) for i in range(len(fa[0]))]
        if 7 in degs: has7=True
        if (10-len(degs))%2: odd=True
    if has7 and odd:
        want[s]=f; print('s=',s,'r=',r,f,flush=True)
