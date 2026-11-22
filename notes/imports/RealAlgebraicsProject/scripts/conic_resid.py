import numpy as np, itertools
n=9
Cs=np.load('curves_deg2.npy')
rng=np.random.default_rng(0)
def good(C):
    return not any(np.linalg.norm(C[i]+C[j])<1e-6 for i in range(n) for j in range(i+1,n)) and min(np.linalg.norm(C,axis=1))>1e-6 and np.linalg.svd(C,compute_uv=False)[-1]>0.02
out=[]
for C in Cs:
    if not good(C): continue
    pt=lambda x,y,z: C[:,0]*x+C[:,1]*y+C[:,2]*z
    # fit p3 = (y^2-xz)*(a x + b y + c z)
    pts=rng.normal(size=(30,3))
    A=np.array([[ (y*y-x*z)*x,(y*y-x*z)*y,(y*y-x*z)*z] for x,y,z in pts])
    bvec=np.array([np.sum(pt(*q)**3) for q in pts])
    l,res,_,_=np.linalg.lstsq(A,bvec,rcond=None)
    fit=np.linalg.norm(A@l-bvec)/np.linalg.norm(bvec)
    # residual line {l.(x,y,z)=0}: basis
    u,s,vt=np.linalg.svd(l.reshape(1,3)); B=vt[1:]
    m0,m1=pt(*B[0]),pt(*B[1])
    ts=np.linspace(-1,1,6)
    p5=[np.sum((m0+t*m1)**5) for t in ts]
    p5c=np.polyfit(ts,p5,5)
    scale=np.max(np.abs(np.polyfit(ts,[np.sum(np.abs(m0+t*m1)**5) for t in ts],5)))
    out.append((fit,np.max(np.abs(p5c))/max(scale,1e-12)))
for o in out: print('%.1e  p5 on residual line rel %.2e'%o)
import sys
sys.argv=['x','0','2','0']
exec(open('conics135.py').read().split('found = []')[0])
k=0;from collections import Counter;cnt=Counter()
for C in Cs:
    if not good(C): continue
    F,J=eqs(C); rk=np.linalg.matrix_rank(J,1e-8)
    typ='a(m in L135)' if out[k][1]<1e-10 else 'b'
    cnt[(typ,rk)]+=1; k+=1
print(cnt)
