import numpy as np
rng=np.random.default_rng(5); n=9
def F(y): return np.array([y.sum(),(y**3).sum(),(y**5).sum(),(y**2).sum()-1])
def J(y): return np.vstack([np.ones(n),3*y**2,5*y**4,2*y])
def ns(A):
    u,s,vt=np.linalg.svd(A); return vt[len(s[s>1e-12]):].T
sigs={};cnt=0
for it in range(3000):
    y=rng.normal(size=n); y/=np.linalg.norm(y)
    for k in range(60):
        y=y-np.linalg.pinv(J(y))@F(y)
    if np.linalg.norm(F(y))>1e-12: continue
    if np.min(np.diff(np.sort(y)))<1e-3: continue
    if min(abs(y[i]+y[j]) for i in range(n) for j in range(i+1,n))<1e-3: continue
    L=ns(np.vstack([np.ones(n),y**2]))
    # mod out y itself (y in L, Q_y(y)=p3=0): quotient form
    M=L.T@np.diag(y)@L
    ev=np.linalg.eigvalsh(M); s=(int((ev>1e-9).sum()),int((ev<-1e-9).sum()))
    sigs[s]=sigs.get(s,0)+1; cnt+=1
print(cnt,sigs)
