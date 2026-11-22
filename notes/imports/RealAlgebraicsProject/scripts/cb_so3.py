"""SO(3)-natural polynomial families through the 9 vectors Q_i (session 30).
Delta(Q) = c1^2 - 4 c0 c2 (discriminant).  Tests rank deficiency."""
import numpy as np, itertools
Qs=np.load('cb_good.npy')
def D(Q): return Q[:,1]**2-4*Q[:,0]*Q[:,2]
def cols(Q,name):
    L=[Q[:,0],Q[:,1],Q[:,2]]; d=D(Q)
    hom2=[Q[:,a]*Q[:,b] for a in range(3) for b in range(a,3)]
    if name=='l+Dl': return L+[d*x for x in L]
    if name=='l+Dl+D2l': return L+[d*x for x in L]+[d*d*x for x in L]
    if name=='1+D+D2': return [np.ones(9),d,d*d]
    if name=='hom2+D2': return hom2+[d*d]
    if name=='1+hom2+D2': return [np.ones(9)]+hom2+[d*d]
    if name=='l+cub': return L+[np.prod(Q**np.array(e),axis=1) for e in itertools.product(range(4),repeat=3) if sum(e)==3]
from collections import Counter
for name in ['l+Dl','l+Dl+D2l','1+D+D2','hom2+D2','1+hom2+D2']:
    c=Counter()
    for Q in Qs:
        M=np.array(cols(Q,name)).T; M=M/np.linalg.norm(M,axis=0)
        s=np.linalg.svd(M,compute_uv=False)
        c[(M.shape[1],int(np.sum(s>1e-9*s[0])))]+=1
    print(name,dict(c))
