import sys
from sigma56 import *
seed=int(sys.argv[1]); rng,Q,v1,v3,lam,m=mk(seed)
eqs=system(Q,v1,v3,lam,m,a="a")
for form in ['y','s']:
    if form=='y': w="+".join(f"({rng.randrange(p)})*y{i+1}" for i in range(9))
    else: w="s"
    sc=f"ring r={p},({VARS},a),dp; ideal I={','.join(eqs)},{w}-({rng.randrange(p)}); ideal G=std(I); print(vdim(G));"
    print(form, run(sc,timeout=600).split())
