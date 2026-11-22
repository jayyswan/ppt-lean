"""Session 31: H = l*K (line x conic). Count the 9 points [q_i] on l and on K,
check l is defined by a relation among exactly 3 coordinates, and test the polar
condition (Delta-pole of l has K-polar l)."""
import numpy as np, itertools
exec(open('pen_sing.py').read().split("Delta=lambda")[0])
from collections import Counter
def ev(coef,x): return sum(c*np.prod(x**np.array(e)) for c,e in zip(coef,mon))
cnt=Counter()
for Q,l in zip(Qs,lab):
    if l!='pencil': continue
    H=cubic_of(Q); S=sings(H,40)
    if len(S)!=2: cnt['nsing',len(S)]+=1; continue
    lin=np.cross(S[0],S[1]); lin/=np.linalg.norm(lin)
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    onl=np.abs(q@lin)<1e-8
    # residual conic: divide H by lin numerically: fit conic K with lin*K = H
    mon2=[e for e in itertools.product(range(3),repeat=3) if sum(e)==2]
    A=[];
    xs=np.random.default_rng(2).normal(size=(30,3))
    A=np.array([[ (x@lin)*np.prod(x**np.array(e)) for e in mon2] for x in xs])
    b=np.array([ev(H,x) for x in xs]); Kc,res,_,_=np.linalg.lstsq(A.astype(complex),b.astype(complex),rcond=None)
    fit=np.linalg.norm(A@Kc-b)/np.linalg.norm(b)
    Kv=np.array([sum(c*np.prod(x**np.array(e)) for c,e in zip(Kc,mon2)) for x in q])
    onK=np.abs(Kv)<1e-8*np.abs(Kc).max()
    # the 3 points on l: relation among 3 coordinates
    cnt[('n on l',int(onl.sum()),'n on K',int(onK.sum()),'both',int((onl&onK).sum()),'fit<1e-10',fit<1e-10, 'l real', np.allclose(lin.imag/abs(lin).max(),0,atol=1e-8))]+=1
print(cnt)
