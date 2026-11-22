import sys, numpy as np
exec(open('quad55.py').read().split("\ndef main")[0])
seed=int(sys.argv[1]); d=np.load(f'quad55_{seed}.npy')
rng,Q,v1,v3,x1=setup(seed)
bad=0
for row in d:
    Qp,x3=row[:9],row[9:18]
    for a,b in [(x1,Qp),(x3,Qp),(Q,x1),(Q,x3)]:
        for lam in [0.3,1.7-0.4j]:
            y=a+lam*b; y=y/np.linalg.norm(y)
            r=max(abs((y**k).sum()) for k in (1,2,3))
            if r>1e-8: bad+=1
    M=np.array([Q,x1,x3,Qp]); sv=np.linalg.svd(M,compute_uv=False)
print('rows',len(d),'bad',bad,'last span sv',sv/sv[0])
