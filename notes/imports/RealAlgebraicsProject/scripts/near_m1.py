"""Session 27: are the special a-lines limits of ordinary lines of S? Perturb and re-solve the line system."""
import numpy as np, sys
from sheets_tan import line_sys
from lp_core import degenerate
X = np.load(sys.argv[1]); rng = np.random.default_rng(3)
def solve(y):
    lam=1e-2; F,J=line_sys(y[:9],y[9:]); f=F@F
    for it in range(600):
        st=np.linalg.solve(J.T@J+lam*np.eye(18),J.T@F); yn=y-st; Fn,Jn=line_sys(yn[:9],yn[9:]); fn=Fn@Fn
        if fn<f: y,F,J,f=yn,Fn,Jn,fn; lam=max(lam/3,1e-12)
        else: lam*=4
        if f<1e-28 or lam>1e9: break
    for it in range(15): y=y-np.linalg.lstsq(J,F,rcond=None)[0]; F,J=line_sys(y[:9],y[9:])
    return y,np.linalg.norm(F),J
def pl(y):  # Plucker vector
    Z,a=y[:9],y[9:]; P=np.outer(Z,a)-np.outer(a,Z); v=P[np.triu_indices(9,1)]; return v/np.linalg.norm(v)
x=X[0]; m1=x[:18]; P1=pl(m1)
for eps in (0.003,0.01,0.03,0.1):
    res={}
    for t in range(12):
        y,r,J=solve(m1+eps*rng.normal(size=18))
        if r>1e-11: res['fail']=res.get('fail',0)+1; continue
        s=np.linalg.svd(J,compute_uv=False); k=18-(s>1e-6*s[0]).sum()
        d=min(np.linalg.norm(pl(y)-P1),np.linalg.norm(pl(y)+P1))
        tag=(k, 'same' if d<1e-6 else ('near' if d<0.3 else 'far'), degenerate(y[:9],y[9:],y[9:]) )
        res[tag]=res.get(tag,0)+1
    print(eps,res)
