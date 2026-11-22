import sys
from sigma56 import *
seed=int(sys.argv[1]); rng,Q,v1,v3,lam,m=mk(seed)
for ex in [True, False]:
  for k in range(2):
    s0=rng.randrange(p)
    eqs=system(Q,v1,v3,lam,m,a="a")
    if not ex: eqs=eqs[:-1]
    sc=f"ring r={p},({VARS},a),dp; ideal I={','.join(eqs)},s-({s0}); ideal G=std(I); print(vdim(G)); print(dim(G));"
    print(ex, s0, run(sc,timeout=600).split())
# a-fibre with the u3 exclusion via a fixed
a0=rng.randrange(p); eqs=system(Q,v1,v3,lam,m,a="a")
sc=f"ring r={p},({VARS},a),dp; ideal I={','.join(eqs)},a-({a0}); ideal G=std(I); print(vdim(G));"
print('afib',run(sc).split())
