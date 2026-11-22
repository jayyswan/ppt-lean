import numpy as np, sys
sys.argv=['x','0','2','0']
exec(open('conics135.py').read().split('found = []')[0])
Cs=np.load('curves_deg2.npy')
def q4poly(C):
    from numpy.polynomial import polynomial as Pl
    p2=sum(Pl.polypow(C[i],2) for i in range(n)); p4=sum(Pl.polypow(C[i],4) for i in range(n))
    return 6*p4-Pl.polymul(p2,p2)
res=[]
for C in Cs:
    npair=sum(np.linalg.norm(C[i]+C[j])<1e-6 for i in range(n) for j in range(i+1,n))
    nz=sum(np.linalg.norm(C,axis=1)<1e-6)
    if npair or nz: continue
    F,J=eqs(C); rk=np.linalg.matrix_rank(J,1e-8)
    q=q4poly(C); r=np.roots(q[::-1]); nreal=sum(abs(z.imag)<1e-8*max(1,abs(z)) for z in r)
    # real projective conic: also t=inf counts via degree; include sign change
    res.append((rk,nreal))
from collections import Counter
print(len(res),Counter(res))
print('---- special ones')
for C in Cs:
    npair=sum(np.linalg.norm(C[i]+C[j])<1e-6 for i in range(n) for j in range(i+1,n))
    nz=sum(np.linalg.norm(C,axis=1)<1e-6)
    neq=sum(np.linalg.norm(C[i]-C[j])<1e-6 for i in range(n) for j in range(i+1,n))
    F,J=eqs(C); rk=np.linalg.matrix_rank(J,1e-8)
    if npair or nz: continue
    print(rk,'equal pairs',neq, 'sv of C', np.round(np.linalg.svd(C,compute_uv=False),4))
    if rk<21:
        # canonical: express coords in an orthonormal basis of the row space
        u,s,vt=np.linalg.svd(C); print(np.round(C@vt.T,4))
