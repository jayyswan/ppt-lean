# Fast, hard-bounded checks:
#  (1) Jacobian rank at a real solution (isolation);
#  (2) degree<=6 relation for Delta with maxcoeff 10^100 at dps=1400 (rule-satisfying).
import mpmath as mp, numpy as np, sys, os, time
sys.stdout.reconfigure(line_buffering=True)
HERE=os.path.dirname(os.path.abspath(__file__))
sols=np.load(os.path.join(HERE,"all-solutions.npy"))
SI=int(sys.argv[1]) if len(sys.argv)>1 else 0
DPS=1400

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
z=[mp.mpf(repr(float(x))) for x in sols[SI]]
for _ in range(100):
    F=res(z)
    if max(abs(v) for v in F)<mp.mpf(10)**(-(DPS+30)): break
    dz=mp.lu_solve(jac(z),F); z=[z[k]-dz[k] for k in range(7)]
F=res(z); print("sol",SI,"max|F|=",mp.nstr(max(abs(v) for v in F),4),flush=True)
sv=mp.svd(jac(z))[1]
print("Jacobian singvals:", [mp.nstr(s,5) for s in sv],flush=True)
D=z[6]; print("Delta=",mp.nstr(D,40),flush=True)
# degree 1..8, maxcoeff 10^100 for d=6 (rule needs (d+1)*100 <= 700  -> ok for d<=6)
for d in range(1,9):
    maxc=10**100 if d<=6 else 10**80
    t0=time.time()
    rel=mp.pslq([D**j for j in range(d+1)], tol=mp.mpf(10)**(-(DPS*3//4)), maxcoeff=maxc, maxsteps=3000)
    if rel:
        H=max(abs(int(v)) for v in rel); val=abs(sum(int(c)*D**j for j,c in enumerate(rel)))
        ok=(d+1)*mp.log10(H)<=mp.mpf(DPS)/2
        print("  d=%d relation log10H=%.1f |p|=%.1e rule_ok=%s (%.1fs)"%(d,float(mp.log10(H)),float(val),ok,time.time()-t0),flush=True)
    else:
        print("  d=%d none (%.1fs)"%(d,time.time()-t0),flush=True)
