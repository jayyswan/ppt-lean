import numpy as np, sys
from hilb import *
sys.argv=['x','0','0']
exec(open('linepairs.py').read().split('good, stats')[0])
x0=np.load('pairs_1.npy')[0]
rng=np.random.default_rng(3)
pts=[x0]
for k in range(6):
    x,r,J=solve(x0+0.05*rng.normal(size=27))
    if r<1e-12 and degenerate(x[:9],x[9:18],x[18:]) is None: pts.append(x)
for x in pts[:4]:
    E=np.stack([x[:9],x[9:18],x[18:]],1); q=np.zeros(6); q[IDX[2][(0,1,1)]]=1.0
    l3,h3,_,_=fit_lh(E,q); u=np.concatenate([E.ravel(),q,l3,h3])
    Jm=jac(u); U,s,Vt=np.linalg.svd(Jm)
    print('svals near gap', np.array2string(s[30:34],precision=2), '| next', s[33]/s[0])
    K=Vt[33:]          # 13-dim kernel
    c=U[:,33]          # cokernel (34 eqs, rank 33)
    h=1e-3
    def D2(v,w):
        return c@(F(u+h*v+h*w)-F(u+h*v-h*w)-F(u-h*v+h*w)+F(u-h*v-h*w))/(4*h*h)
    Q=np.array([[D2(K[i],K[j]) for j in range(13)] for i in range(13)])
    ev=np.linalg.eigvalsh((Q+Q.T)/2)
    print('  obstruction form eigenvalues on 13-dim kernel:', np.array2string(ev[np.argsort(-abs(ev))][:4],precision=3))
    # direction of the line-pair curve: tangent of the line-pair family, mapped to u-coords
    xs,_,Jl=solve(x); Ul,sl,Vl=np.linalg.svd(Jl); t=Vl[-1]  # approx (kernel of rank-24 J is 3-dim; use displacement instead)
