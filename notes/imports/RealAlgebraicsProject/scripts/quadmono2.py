"""Track selected sheets of quad55's fibre around large loops (does sheet i ever move?).
Usage: quadmono2.py <seed> <loops> <steps> <radius> <tag> <i,j,...>"""
import sys, numpy as np
src=open('quadmono.py').read().split("rs=np.random.default_rng")[0]
exec(src)
idx=[int(x) for x in sys.argv[6].split(',')]
R=float(sys.argv[4]); steps=int(sys.argv[3])
rs=np.random.default_rng(1000+int(sys.argv[5]))
for L in range(int(sys.argv[2])):
    c=a0+(rs.standard_normal()+1j*rs.standard_normal())*R
    th=np.linspace(0,2*np.pi,steps); path=c+(a0-c)*np.exp(1j*th)
    out=[]
    for i in idx:
        zz=track(Z0[i].copy(),path)
        if zz is None: out.append('fail'); continue
        k=key(zz,a0); dist=[np.linalg.norm(k-k0) for k0 in K0]; j=int(np.argmin(dist))
        out.append(j if dist[j]<1e-6 else 'lost')
    print('loop',L,'|c-a0|=%.2f'%abs(c-a0), dict(zip(idx,out)), flush=True)
