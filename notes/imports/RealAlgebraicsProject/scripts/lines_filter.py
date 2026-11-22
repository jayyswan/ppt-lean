"""Session 34: filter real lines from `conics135b.py <seed> 1 <starts>` output
(curves_deg1_s<seed>.npy): drop zero/paired coordinates, label E vs ordinary by
the conic-rank test (sv4 of [1, Z^2, Za, a^2] below 1e-3 = E).
Writes lines_good.npy and lines_lab.npy ('gen' = S_ord, 'E')."""
import numpy as np, sys
L=np.load(sys.argv[1] if len(sys.argv)>1 else 'curves_deg1_s21.npy'); n=9; keep=[];kind=[]
for C in L:
    if min(np.linalg.norm(C,axis=1))<1e-4: continue
    if any(np.linalg.norm(C[i]+C[j])<1e-4 for i in range(n) for j in range(i+1,n)): continue
    Z,a=C[:,0],C[:,1]
    M=np.array([np.ones(n),Z*Z,Z*a,a*a]).T; M/=np.linalg.norm(M,axis=0)
    s=np.linalg.svd(M,compute_uv=False)
    keep.append(C); kind.append('gen' if s[-1]>1e-3 else 'E')
print(len(keep), 'ordinary', kind.count('gen'), 'E', kind.count('E'))
np.save('lines_good.npy',np.array(keep)); np.save('lines_lab.npy',np.array(kind))
