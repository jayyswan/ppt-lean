import numpy as np, sys
from hilb import *
sys.argv=['x','0','0']
exec(open('linepairs.py').read().split('good, stats')[0])
x0=np.load('pairs_1.npy')[0]
rng=np.random.default_rng(3)
pts=[x0]
for k in range(8):
    x,r,J=solve(x0+0.05*rng.normal(size=27))
    if r<1e-12 and degenerate(x[:9],x[9:18],x[18:]) is None: pts.append(x)
for x in pts[:6]:
    Z,a,b=x[:9],x[9:18],x[18:]
    E=np.stack([Z,a,b],1)
    q=np.zeros(6); q[IDX[2][(0,1,1)]]=1.0   # q = y*z : the two lines y=0 (Z+t b) and z=0 (Z+s a)
    l3,h3,r3,r5=fit_lh(E,q)
    u=np.concatenate([E.ravel(),q,l3,h3])
    kd,s=kernel_dim(u)
    print('fit res %.1e %.1e'%(r3,r5),' |F|=%.1e'%np.linalg.norm(F(u)),' kernel dim',kd,' sv tail',np.array2string(s[-14:-8],precision=1),
          ' p5 on residual line m\': %.2e'%p5_on_line(E,l3))
