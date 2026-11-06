# Same fast degree test for a SECOND totally real septic, to show the >6 (indeed >8)
# auxiliary degree is not special to the S_7 test target.
# Usage: 12-second-septic.py "1,0,-7,0,14,0,-7,1"
import mpmath as mp, numpy as np, sys, os
sys.stdout.reconfigure(line_buffering=True)
coefs=[int(x) for x in sys.argv[1].split(',')]
deg=len(coefs)-1
DPS=1000
print("f coefficients:",coefs,flush=True)
def f(t):
    return sum(c*t**(deg-i) for i,c in enumerate(coefs))
def fp(t):
    return sum((deg-i)*c*t**(deg-i-1) for i,c in enumerate(coefs))
# double roots
r0=np.sort(np.roots(coefs).real)
# solve system in double
from scipy.optimize import root as scroot
def mk(r):
    def res(z):
        a,b,c,p,q,rr,D=z; out=np.empty(deg)
        for i,t in enumerate(r):
            u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr
            out[i]=u*u*(up*up+vq*vq)-D*vq*vq
        return out
    def jac(z):
        a,b,c,p,q,rr,D=z; J=np.zeros((deg,7))
        for i,t in enumerate(r):
            u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr; S=up*up+vq*vq
            J[i]=[2*u*t*t*S+u*u*(4*up*t),2*u*t*S+u*u*(2*up),2*u*S,
                  2*(u*u-D)*vq*t*t,2*(u*u-D)*vq*t,2*(u*u-D)*vq,-vq*vq]
        return J
    return res,jac
res,jac=mk(r0)
rng=np.random.default_rng(3); sols=[]
for _ in range(12000):
    z0=np.array([rng.uniform(-6,6),rng.uniform(-12,12),rng.uniform(-10,10),
                 rng.uniform(-3,3),rng.uniform(-12,12),rng.uniform(-12,12),10**rng.uniform(-1,3)])
    try:
        s=scroot(res,z0,jac=jac,method='hybr',options={'maxfev':6000})
    except Exception: continue
    if s.success and np.linalg.norm(res(s.x))<1e-8:
        if all(np.linalg.norm(s.x-y)>1e-4 for y in sols): sols.append(s.x.copy())
print("real solutions:",len(sols),flush=True)
# high precision roots
mp.mp.dps=DPS+60
rts=[]
for x0 in r0:
    x=mp.mpf(repr(float(x0)))
    for _ in range(500):
        dx=f(x)/fp(x); x=x-dx
        if abs(dx)<mp.mpf(10)**(-(DPS+20)): break
    rts.append(x)
rts=sorted(rts)
def hres(z):
    a,b,c,p,q,rr,D=z; out=[]
    for t in rts:
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr
        out.append(u*u*(up*up+vq*vq)-D*vq*vq)
    return mp.matrix(out)
def hjac(z):
    a,b,c,p,q,rr,D=z; M=mp.zeros(deg,7)
    for i,t in enumerate(rts):
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr; S=up*up+vq*vq
        M[i,0]=2*u*t*t*S+u*u*(4*up*t); M[i,1]=2*u*t*S+u*u*(2*up); M[i,2]=2*u*S
        M[i,3]=2*(u*u-D)*vq*t*t; M[i,4]=2*(u*u-D)*vq*t; M[i,5]=2*(u*u-D)*vq; M[i,6]=-vq*vq
    return M
seen=[]
for s in sols:
    if any(abs(s[6]-y[6])<1e-4 for y in seen): continue
    z=[mp.mpf(repr(float(x))) for x in s]
    for _ in range(80):
        F=hres(z)
        if max(abs(v) for v in F)<mp.mpf(10)**(-(DPS+30)): break
        dz=mp.lu_solve(hjac(z),F); z=[z[k]-dz[k] for k in range(7)]
    seen.append(z)
print("distinct Delta:",len(seen),flush=True)
for z in seen:
    D=z[6]; D=z[6]
    rel=mp.pslq([D**j for j in range(7)], tol=mp.mpf(10)**-(3*DPS//4), maxcoeff=10**70, maxsteps=3000)
    tag="none" if not rel else "REL deg<=6"
    print("  Delta=%s -> %s"%(mp.nstr(D,16),tag),flush=True)
