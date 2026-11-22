"""Perturb-and-resolve near conics of each population: does the cubic-pencil
property persist (=> a separate component)?  Session 30."""
import numpy as np, itertools, sys
sys.argv=['x','0','2']
exec(open('conics135b.py').read().split("if __name__")[0])
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
mon=[e for e in itertools.product(range(4),repeat=3) if sum(e)==3]
def pen(Q):
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([[np.prod(x**np.array(e)) for e in mon] for x in q])
    s=np.linalg.svd(M,compute_uv=False); return s[-1]/s[0]
def newton(x):
    for it in range(30):
        F,J=FJ(x); x=x-np.linalg.lstsq(J,F,rcond=None)[0]
    return x, np.linalg.norm(FJ(x)[0])
rng=np.random.default_rng(5)
for t in ['pencil','gen']:
    idx=[i for i in range(len(Qs)) if lab[i]==t][:4]
    for i in idx:
        x0=Qs[i].ravel()/np.linalg.norm(Qs[i])
        F,J=FJ(x0); u,s,vt=np.linalg.svd(J); K=vt[np.sum(s>1e-8*s[0]):]
        vals=[]
        for eps in [0.02,0.05,0.1]:
            x=x0+eps*(K.T@rng.normal(size=len(K)))
            x,r=newton(x)
            vals.append('%.0e(res %.0e)'%(pen(x.reshape(9,3)),r))
        print(t,i,' '.join(vals))
