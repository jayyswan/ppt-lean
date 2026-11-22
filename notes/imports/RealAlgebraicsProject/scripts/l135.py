import numpy as np
rng=np.random.default_rng(1)
def F(z): return np.array([z.sum(),(z**3).sum(),(z**5).sum(),(z**2).sum()-1])
def J(z): return np.vstack([np.ones(9),3*z**2,5*z**4,2*z])
vals=[]
for _ in range(4000):
    z=rng.normal(size=9); z-=z.mean(); z/=np.linalg.norm(z)
    for it in range(60):
        f=F(z)
        if np.linalg.norm(f)<1e-13: break
        z=z-np.linalg.lstsq(J(z),f,rcond=None)[0]
    if np.linalg.norm(F(z))<1e-12 and len(set(np.round(z,6)))==9:
        p2=(z**2).sum(); p4=(z**4).sum(); vals.append(6*p4/p2**2)
v=np.array(vals); print(len(v), v.min(), v.max(), (v<1).mean())
