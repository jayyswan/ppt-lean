"""Session 27: does a line meet Sing(L_135)? minimise sigma_min of grad(p1,p3,p5) over complex s."""
import numpy as np, sys
from scipy.optimize import minimize
X=np.load(sys.argv[1])
def smin(Z,v,s):
    z=Z+s*v; z=z/np.linalg.norm(z)
    G=np.stack([np.ones(9),3*z**2,5*z**4]); return np.linalg.svd(G,compute_uv=False)[-1]
rng=np.random.default_rng(1)
for x in X[:3]:
    Z,a,b=x[:9],x[9:18],x[18:]
    for nm,v in (('a',a),('b',b)):
        best=9
        for t in range(40):
            r=minimize(lambda p: smin(Z,v,p[0]+1j*p[1]),rng.normal(size=2)*1.5,method='Nelder-Mead',options={'xatol':1e-12,'fatol':1e-14,'maxiter':4000})
            best=min(best,r.fun)
        # also s=infinity end: point v itself
        print(nm,'min sigma',best,' at infinity',smin(v,Z,0))
