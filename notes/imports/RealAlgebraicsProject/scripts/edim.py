"""Session 27: local dimension of the family E of special lines near the a-line m1."""
import numpy as np, sys
exec(open('near_m1.py').read().split("x=X[0]")[0])
x=X[0]; m1=x[:18]; P1=pl(m1)
for eps in (0.01,0.03):
    D=[]
    for t in range(40):
        y,r,J=solve(m1+eps*rng.normal(size=18))
        if r>1e-11: continue
        p=pl(y); p = p if p@P1>0 else -p
        D.append(p-P1)
    D=np.array(D); print(eps,len(D),np.round(np.linalg.svd(D,compute_uv=False)[:7]/len(D)**.5,6))
