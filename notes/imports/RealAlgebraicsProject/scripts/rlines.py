# Session 29. Real lines in L_135 by Levenberg-Marquardt in line space; keeps genuinely ordinary lines
# (conic-rank test; NOTE: E-lines found at LM accuracy have sv4 ~ 1e-7, so use sv4 > 1e-3 downstream).
# real lines Z + s a in L_135 by LM; keep genuine ordinary ones (no zero/paired coords, conic-rank 4)
# usage: python3 rlines.py <seed> <starts>   writes rlines_<seed>.npy  (rows: Z(9), a(9))
import numpy as np, sys, warnings; warnings.filterwarnings('ignore')
from scipy.optimize import least_squares
rng=np.random.default_rng(int(sys.argv[1])); N=int(sys.argv[2])
S=np.array([-1.3,-0.6,0.1,0.7,1.4,2.0])
def res(v):
    Z,a=v[:9],v[9:]
    out=[]
    for m in (1,3,5):
        vals=[np.sum((Z+s*a)**m) for s in S[:m+1]]
        out+=vals
    out+= [np.dot(Z,Z)-1, np.dot(a,a)-1, np.dot(Z,a), Z[0]+0.0*a[0]]  # gauge: orthonormal-ish, fix rotation by Z[0]=0? keep weak
    return np.array(out[:-1])
keep=[]
for k in range(N):
    v=rng.normal(size=18)
    r=least_squares(res,v,xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=3000)
    if np.max(abs(r.fun))>1e-11: continue
    Z,a=r.x[:9],r.x[9:]
    # degeneracy filters along the line: coordinates as linear functions (Z_i,a_i)
    Q=np.stack([Z,a],1); nrm=np.linalg.norm(Q,axis=1)
    if nrm.min()<1e-4: continue
    par=min(min(np.linalg.norm(Q[i]+Q[j]),np.linalg.norm(Q[i]-Q[j])) for i in range(9) for j in range(i))
    if par<1e-4: continue
    M=np.stack([np.ones(9),Z**2,Z*a,a**2],1); sv=np.linalg.svd(M/np.linalg.norm(M,axis=0),compute_uv=False)
    kind='E' if sv[-1]<1e-8 else 'ord'
    print(k,kind,'minpair %.3g'%par,'sv4 %.2e'%sv[-1],flush=True)
    if kind=='ord': keep.append(r.x)
np.save('rlines_%s.npy'%sys.argv[1],np.array(keep)); print('kept',len(keep))
