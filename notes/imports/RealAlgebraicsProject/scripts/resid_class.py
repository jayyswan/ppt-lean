"""Session 26: for generic real conics on L_135 (output of conics135.py <seed> 2 <starts>), find the
residual line m of p3 in the conic's plane and record (m in L_135?, pairing pattern of m).
Result (2 x 160 starts, 78 generic conics): every m inside L_135 lies in a pairing P^3 or a one-pair hyperplane."""
import numpy as np, glob
from collections import Counter
n=9; rng=np.random.default_rng(0)
def good(C):
    return not any(np.linalg.norm(C[i]+C[j])<1e-6 for i in range(n) for j in range(i+1,n)) and min(np.linalg.norm(C,axis=1))>1e-6 and np.linalg.svd(C,compute_uv=False)[-1]>0.02
def residual(C):
    pt=lambda x,y,z: C[:,0]*x+C[:,1]*y+C[:,2]*z
    pts=rng.normal(size=(30,3))
    A=np.array([[(y*y-x*z)*x,(y*y-x*z)*y,(y*y-x*z)*z] for x,y,z in pts])
    b=np.array([np.sum(pt(*q)**3) for q in pts])
    l=np.linalg.lstsq(A,b,rcond=None)[0]
    B=np.linalg.svd(l.reshape(1,3))[2][1:]
    L=np.stack([pt(*B[0]),pt(*B[1])],1); return L/np.linalg.norm(L)
def p5rel(L):
    ts=np.linspace(-1,1,7)
    c=np.polyfit(ts,[np.sum((L[:,0]+t*L[:,1])**5) for t in ts],5)
    s=np.polyfit(ts,[np.sum(np.abs(L[:,0]+t*L[:,1])**5) for t in ts],5)
    return np.max(abs(c))/np.max(abs(s))
def struct(L):
    z=sum(np.linalg.norm(L[i])<1e-6 for i in range(9))
    p=sum(np.linalg.norm(L[i]+L[j])<1e-6 for i in range(9) for j in range(i+1,9) if np.linalg.norm(L[i])>1e-6)
    return (int(p),int(z))
cnt=Counter()
for f in sorted(glob.glob('curves_deg2*.npy')):
    for C in np.load(f):
        if not good(C): continue
        L=residual(C); inL=p5rel(L)<1e-9
        cnt[('m in L135' if inL else 'm not in L135', struct(L))]+=1
for k,v in sorted(cnt.items()): print(k,v)
