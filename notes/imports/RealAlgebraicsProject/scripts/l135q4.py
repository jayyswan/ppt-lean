import numpy as np
rng=np.random.default_rng(2)
def F(z): p=lambda k:(z**k).sum(); return np.array([p(1),p(3),p(5),6*p(4)-p(2)**2,p(2)-1])
def J(z): return np.vstack([np.ones(9),3*z**2,5*z**4,24*z**3-4*(z**2).sum()*z,2*z])
ok=0;ex=None
for _ in range(500):
    z=rng.normal(size=9); z-=z.mean(); z/=np.linalg.norm(z)
    for it in range(80):
        f=F(z)
        if np.linalg.norm(f)<1e-14: break
        z=z-np.linalg.lstsq(J(z),f,rcond=None)[0]
    if np.linalg.norm(F(z))<1e-12 and np.min(np.diff(np.sort(z)))>1e-4:
        ok+=1; ex=np.sort(z)
print(ok, ex, np.linalg.matrix_rank(J(ex)))
