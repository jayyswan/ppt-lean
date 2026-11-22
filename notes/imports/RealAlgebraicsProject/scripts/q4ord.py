# Session 29. Real roots of Q4 restricted to real ordinary lines.  usage: python3 q4ord.py rlines_*.npy
# Q4 = 6 p4 - p2^2 restricted to real ordinary lines Z + s a: real roots?  Also p7 (septic) real roots.
import numpy as np, sys
rows=np.concatenate([np.load(f) for f in sys.argv[1:]])
cnt={};n=0;nh1=0
for v in rows:
    Z,a=v[:9],v[9:]
    M=np.stack([np.ones(9),Z**2,Z*a,a**2],1); sv=np.linalg.svd(M/np.linalg.norm(M,axis=0),compute_uv=False)
    if sv[-1]<1e-3: continue
    n+=1
    # Q4 as quartic in s via interpolation
    ss=np.linspace(-2,2,9); vals=[6*np.sum((Z+s*a)**4)-np.sum((Z+s*a)**2)**2 for s in ss]
    q=np.polyfit(ss,vals,4); r=np.roots(q); nr=np.sum(abs(r.imag)<1e-8*np.max(abs(r)))
    p7=np.polyfit(np.linspace(-2,2,15),[np.sum((Z+s*a)**7) for s in np.linspace(-2,2,15)],7)
    cnt[nr]=cnt.get(nr,0)+1
    # also: min over s of 6p4/p2^2 along the line (Q4<0 needs ratio<1)
print('ordinary lines',n,' # real roots of Q4|line ->',cnt)
