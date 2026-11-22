import numpy as np, sys
sys.argv=['x','0','0']
exec(open('linepairs.py').read().split('good, stats')[0])
x0=np.load('pairs_1.npy')[0]
rng=np.random.default_rng(7)
def canon(x):
    Z,a,b=x[:9],x[9:18],x[18:]
    if Z@x0[:9]<0: Z=-Z
    if a@x0[9:18]<0: a=-a
    if b@x0[18:]<0: b=-b
    return np.concatenate([Z,a,b])
pts=[]
for k in range(60):
    x,r,J=solve(x0+0.02*rng.normal(size=27))
    if r<1e-12 and degenerate(x[:9],x[9:18],x[18:]) is None:
        x=canon(x)
        if np.linalg.norm(x-x0)<0.1: pts.append(x)
P=np.array(pts)-x0
print(len(pts), 'sv of displacement matrix:', np.array2string(np.linalg.svd(P,compute_uv=False)[:6],precision=4))
# tangent from J null space
x,r,J=solve(x0); U,s,Vt=np.linalg.svd(J); N=Vt[-3:]
proj=P@N.T; print('fraction of displacement in 3-dim J-kernel:', np.linalg.norm(proj)/np.linalg.norm(P))
