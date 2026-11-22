# Session 29. Converts real ordinary lines (rlines_*.npy) to Weierstrass data (h, x_i) via the odd cubic
# and checks the criterion F(x_i)^2 / h(x_i)^5 = const.  usage: python3 conv.py rlines_1.npy rlines_2.npy
# convert real ordinary lines (rlines_*.npy) to Weierstrass data and test F'(x_i)^2 / h(x_i)^5 = const
import numpy as np, sys, glob
rows=np.concatenate([np.load(f) for f in sys.argv[1:]])
out=[]
for v in rows:
    Z,a=v[:9],v[9:]
    M=np.stack([np.ones(9),Z**2,Z*a,a**2],1); sv=np.linalg.svd(M/np.linalg.norm(M,axis=0),compute_uv=False)
    if sv[-1]<1e-3: continue  # E-line
    A=np.stack([Z,a,Z**3,Z**2*a,Z*a**2,a**3],1)
    u,s,vt=np.linalg.svd(A); g=vt[-1]   # odd cubic coefficients
    al,be=g[0],g[1]; n=np.hypot(al,be)
    Zp=(al*Z+be*a)/n; ap=(-be*Z+al*a)/n
    # rewrite cubic in (Zp,ap): solve g(Z,a)=Zp*n + c3(Z,a); fit c3' directly: Zp + c3'(Zp,ap) = 0 on points
    B=np.stack([Zp**3,Zp**2*ap,Zp*ap**2,ap**3],1)
    c3p=np.linalg.lstsq(B,-Zp,rcond=None)[0]
    fitres=np.linalg.norm(B@c3p+Zp)
    x=ap/Zp; y=1/Zp
    hc=-c3p   # h(x) = -(c30 + c21 x + c12 x^2 + c03 x^3)
    h=lambda t: hc[0]+hc[1]*t+hc[2]*t**2+hc[3]*t**3
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,1); Fp=np.prod(D,axis=1)
    ratio=Fp**2/h(x)**5
    roots=np.roots(hc[::-1])
    print('fit %.1e | y^2-h %.1e | ratio spread %.1e | h roots'%(fitres,np.max(abs(y**2-h(x))/y**2),np.std(ratio)/abs(np.mean(ratio))),
          np.round(np.sort_complex(roots),3),' lead %.2f'%hc[3],' x sorted',np.round(np.sort(x),3))
    out.append((hc,x,np.mean(ratio)))
import pickle; pickle.dump(out,open('conv.pkl','wb'))
