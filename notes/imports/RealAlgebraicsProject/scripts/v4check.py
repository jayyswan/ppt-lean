# Session 51: what engine does V_4 = {p1=..=p4=0} feed in degree n? (charpoly of a real point)
import sys, numpy as np
n=int(sys.argv[1]); r=int(sys.argv[2]); s=(n-r)//2; rng=np.random.default_rng(int(sys.argv[3]))
def zc(u):
    w=u[r::2]+1j*u[r+1::2]; return np.concatenate([u[:r].astype(complex),w,np.conj(w)])
def F(u):
    z=zc(u); return np.array([np.sum(z**k).real for k in (1,2,3,4)]+[u@u-1])
for t in range(200):
    u=rng.normal(size=n)
    for it in range(100):
        f=F(u); J=np.array([(F(u+h)-F(u-h))/2e-7 for h in np.eye(n)*1e-7]).T
        u=u+np.linalg.lstsq(J,-f,rcond=None)[0]
        if np.linalg.norm(f)<1e-14: break
    if np.isfinite(u).all() and np.linalg.norm(F(u))<1e-12: break
z=zc(u); c=np.poly(z).real
print('n',n,'r',r,'power sums p1..p6:',[round(np.sum(z**k).real,10) for k in range(1,7)])
print('charpoly coefficients x^n..x^0:',np.round(c,6))
print('nonzero coefficients at degrees:',[n-i for i,x in enumerate(c) if abs(x)>1e-9])
