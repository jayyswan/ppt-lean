# Single-shot integer-relation search for Delta: one LLL over [1, D, ..., D^MAXD].
import mpmath as mp, numpy as np, sys, os, time
sys.stdout.reconfigure(line_buffering=True)
HERE=os.path.dirname(os.path.abspath(__file__))
DPS=int(sys.argv[1]) if len(sys.argv)>1 else 1000
MAXD=int(sys.argv[2]) if len(sys.argv)>2 else 30
SI=int(sys.argv[3]) if len(sys.argv)>3 else 0
sols=np.load(os.path.join(HERE,"all-solutions.npy"))
s=sols[SI]

def f(t):  return t**7 - 14*t**5 + 49*t**3 - 36*t + 1
def fp(t): return 7*t**6 - 70*t**4 + 147*t**2 - 36
mp.mp.dps=DPS+60
seedr=np.roots([1,0,-14,0,49,0,-36,1]).real
rts=[]
for x0 in seedr:
    x=mp.mpf(repr(float(x0)))
    for _ in range(500):
        dx=f(x)/fp(x); x=x-dx
        if abs(dx)<mp.mpf(10)**(-(DPS+20)): break
    rts.append(x)
rts=sorted(rts)
def res(z):
    a,b,c,p,q,rr,D=z; out=[]
    for t in rts:
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr
        out.append(u*u*(up*up+vq*vq)-D*vq*vq)
    return mp.matrix(out)
def jac(z):
    a,b,c,p,q,rr,D=z; M=mp.zeros(7,7)
    for i,t in enumerate(rts):
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr; S=up*up+vq*vq
        M[i,0]=2*u*t*t*S+u*u*(4*up*t); M[i,1]=2*u*t*S+u*u*(2*up); M[i,2]=2*u*S
        M[i,3]=2*(u*u-D)*vq*t*t; M[i,4]=2*(u*u-D)*vq*t; M[i,5]=2*(u*u-D)*vq; M[i,6]=-vq*vq
    return M
z=[mp.mpf(repr(float(x))) for x in s]
for _ in range(80):
    F=res(z); 
    if max(abs(v) for v in F)<mp.mpf(10)**(-(DPS+30)): break
    dz=mp.lu_solve(jac(z),F); z=[z[k]-dz[k] for k in range(7)]
D=z[6]
print("Delta=",mp.nstr(D,30),flush=True)
t0=time.time()
rel=mp.pslq([D**j for j in range(MAXD+1)], tol=mp.mpf(10)**(-(3*DPS//4)), maxcoeff=10**int(DPS*0.35), maxsteps=2000)
print("one-shot pslq maxdeg=%d time=%.1fs"%(MAXD,time.time()-t0),flush=True)
if rel:
    rel=[int(v) for v in rel]
    H=max(abs(v) for v in rel)
    deg=max(i for i,v in enumerate(rel) if v!=0)
    val=abs(sum(c*D**i for i,c in enumerate(rel)))
    print("relation degree=%d log10H=%.1f |p(D)|=%.1e"%(deg,float(mp.log10(H)),float(val)),flush=True)
    print("coeffs=",rel,flush=True)
else:
    print("no relation found",flush=True)
