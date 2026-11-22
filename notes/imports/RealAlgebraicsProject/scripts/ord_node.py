"""Session 32: real S_ord samples near the node. For h = A(x-e)((x-b1)^2+beta^2):
prints beta/scale, whether the pinch is a crunode (b1 on the h>0 side) or an acnode,
and the 9 points in the node's local coordinate (x_i - b1)/beta, plus |x| of the point nearest O.
usage: python3 ord_node.py rlines_*.npy"""
import numpy as np, sys
rows=np.concatenate([np.load(f) for f in sys.argv[1:]])
for v in rows:
    Z,a=v[:9],v[9:]
    M=np.stack([np.ones(9),Z**2,Z*a,a**2],1); sv=np.linalg.svd(M/np.linalg.norm(M,axis=0),compute_uv=False)
    if sv[-1]<1e-3: continue
    A=np.stack([Z,a,Z**3,Z**2*a,Z*a**2,a**3],1)
    g=np.linalg.svd(A)[2][-1]; al,be=g[0],g[1]; nn=np.hypot(al,be)
    Zp=(al*Z+be*a)/nn; ap=(-be*Z+al*a)/nn
    B=np.stack([Zp**3,Zp**2*ap,Zp*ap**2,ap**3],1)
    hc=-np.linalg.lstsq(B,-Zp,rcond=None)[0]; x=ap/Zp
    r=np.roots(hc[::-1]); e=r[np.argmin(abs(r.imag))].real; cp=r[np.argmax(r.imag)]
    b1,beta=cp.real,abs(cp.imag)
    side=np.sign(np.polyval(hc[::-1],b1+1e-9)) if False else np.sign(hc[3]*(b1-e))
    kind='crunode' if side>0 else 'acnode'
    loc=np.sort((x-b1)/beta)
    scale=abs(b1-e)
    print(f"beta/|b1-e| {beta/scale:.1e} {kind:8s} near-node pts {(np.abs(loc)<30).sum()} | (x-b1)/beta:",
          np.array2string(loc,precision=2,max_line_width=200,suppress_small=True))
