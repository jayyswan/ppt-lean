"""Session 31: the line l carrying 5 of the q_i on C_b^pen. Tangency of l to
Delta, and the binary data (a_i,b_i) of the 5 collinear Q_i = a_i A + b_i B."""
import numpy as np, itertools
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
Ainv=np.array([[0,0,-.5],[0,1,0],[-.5,0,0]])
for Q,lb in zip(Qs,lab):
    if lb!='pencil': continue
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    best=None
    for t in itertools.combinations(range(9),2):
        n_=np.cross(q[t[0]],q[t[1]]); n_/=np.linalg.norm(n_)
        I=np.where(abs(q@n_)<1e-8)[0]
        if len(I)==5: best=(n_,I); break
    n_,I=best; J=[j for j in range(9) if j not in I]
    U=np.linalg.svd(Q[I])[2][:2]          # basis A,B of span
    ab=Q[I]@U.T                            # (a_i,b_i)
    tang=n_@Ainv@n_
    s1=np.linalg.norm(ab.sum(0))/np.linalg.norm(ab)
    s1J=np.linalg.norm(Q[J].sum(0))/np.linalg.norm(Q[J])
    # does span{A,B} contain a square (tangency) / what are binary roots of A,B
    print('|I|',len(I),' l.Ainv.l %.3f'%tang,' |sum over I|/|.| %.2e'%s1,' |sum over J| %.2e'%s1J)
