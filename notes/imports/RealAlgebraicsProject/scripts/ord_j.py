"""Session 32: j-invariants of real S_ord samples. usage: python3 ord_j.py rlines_*.npy"""
import numpy as np, sys
rows=np.concatenate([np.load(f) for f in sys.argv[1:]])
js=[]
for v in rows:
    Z,a=v[:9],v[9:]
    M=np.stack([np.ones(9),Z**2,Z*a,a**2],1); sv=np.linalg.svd(M/np.linalg.norm(M,axis=0),compute_uv=False)
    if sv[-1]<1e-3: continue
    A=np.stack([Z,a,Z**3,Z**2*a,Z*a**2,a**3],1)
    g=np.linalg.svd(A)[2][-1]; al,be=g[0],g[1]; nn=np.hypot(al,be)
    Zp=(al*Z+be*a)/nn; ap=(-be*Z+al*a)/nn
    B=np.stack([Zp**3,Zp**2*ap,Zp*ap**2,ap**3],1)
    hc=-np.linalg.lstsq(B,-Zp,rcond=None)[0]
    d,c,b,A3=hc[0],hc[1],hc[2],hc[3]          # h = A3 x^3 + b x^2 + c x + d
    # depress: x = t - b/(3A3); h/A3 = t^3 + p t + q
    p=(3*A3*c-b*b)/(3*A3*A3); q=(2*b**3-9*A3*b*c+27*A3*A3*d)/(27*A3**3)
    j=1728*4*p**3/(4*p**3+27*q*q)
    js.append(j)
js=np.array(js); print(len(js),'samples; j sorted:'); print(np.round(np.sort(js),1))
