import numpy as np, itertools
Qs=np.load('cb_good.npy')
mon=[e for e in itertools.product(range(4),repeat=3) if sum(e)==3]
out=[]
for k,Q in enumerate(Qs):
    # normalize projective points to unit vectors (projective test)
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([[np.prod(x**np.array(e)) for e in mon] for x in q])
    s=np.linalg.svd(M,compute_uv=False)
    out.append((s[-1]/s[0],k))
out.sort()
print(' '.join('%.1e'%o[0] for o in out))
