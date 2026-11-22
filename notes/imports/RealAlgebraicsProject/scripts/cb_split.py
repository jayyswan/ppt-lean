"""Split C_b samples by whether the 9 points [Q_i] are the base locus of a
pencil of plane cubics; report the Jacobian rank of the conic system. Session 30."""
import numpy as np, itertools, sys
sys.argv=['x','0','2']
exec(open('conics135b.py').read().split("if __name__")[0])
Qs=np.load('cb_good.npy')
mon=[e for e in itertools.product(range(4),repeat=3) if sum(e)==3]
def pen(Q):
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([[np.prod(x**np.array(e)) for e in mon] for x in q])
    s=np.linalg.svd(M,compute_uv=False); return s[-1]/s[0]
from collections import Counter
c=Counter(); lab=[]
for Q in Qs:
    F,J=eqs(Q); s=np.linalg.svd(J,compute_uv=False)
    rk=int(np.sum(s>1e-8*s[0]))
    t='pencil' if pen(Q)<1e-10 else 'gen'
    lab.append(t); c[(t,rk)]+=1
print(c)
np.save('cb_lab.npy',np.array(lab))
