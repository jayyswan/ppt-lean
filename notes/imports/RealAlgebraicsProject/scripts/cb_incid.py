"""Session 31: incidence survey of the 9 points [q_i] in P^2 for all C_b samples:
max number on a line (collinear triples), number of 6-subsets on a conic."""
import numpy as np, itertools
from collections import Counter
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
c=Counter()
for Q,l in zip(Qs,lab):
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    tri=[t for t in itertools.combinations(range(9),3) if abs(np.linalg.det(q[list(t)]))<1e-9]
    # max points on a line
    mx=2
    for t in tri:
        n_=np.cross(q[t[0]],q[t[1]]); n_/=np.linalg.norm(n_)
        mx=max(mx,int(np.sum(abs(q@n_)<1e-8)))
    six=0
    for s in itertools.combinations(range(9),6):
        x=q[list(s)]; M=np.array([[a*a,b*b,d*d,a*b,a*d,b*d] for a,b,d in x])
        sv=np.linalg.svd(M,compute_uv=False)
        if sv[-1]/sv[0]<1e-9: six+=1
    c[(l,'collinear triples',len(tri),'max on line',mx,'6 on conic',six)]+=1
for k,v in sorted(c.items(),key=str): print(k,v)
