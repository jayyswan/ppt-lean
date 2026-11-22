# fibre degree of Sigma -> l1 at many a, factor degrees mod p; common subset sums
import sys
from sigma56 import *
seed=int(sys.argv[1]); n=int(sys.argv[2])
rng,Q,v1,v3,lam,m=mk(seed)
common=None
for k in range(n):
    a0=rng.randrange(p)
    eqs=system(Q,v1,v3,lam,m,a="a")+[f"a-({a0})"]
    w="+".join(f"({rng.randrange(p)})*y{i+1}" for i in range(9))+f"+({rng.randrange(p)})*s"
    o=run(elim_script(eqs,w)).split()
    degs=[int(t.split('^')[0]) for t in o[3:] if not t.startswith('0^')]
    ss={0}
    for d in degs: ss|={x+d for x in ss}
    common=ss if common is None else common&ss
    print(a0,o[0],o[1],degs)
print("common subset sums:",sorted(common))
