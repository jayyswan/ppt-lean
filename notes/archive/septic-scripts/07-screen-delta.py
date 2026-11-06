# Fast Phase 0 screen: for every real solution, is Delta of degree <= 6 over Q?
# A K-point would need Delta in K; if deg(Delta)>6 for all real solutions, the decic
# route gives no K-point (modulo K containing higher-degree reals via other engines).
import mpmath as mp, numpy as np, sys, os, time
sys.stdout.reconfigure(line_buffering=True)
HERE = os.path.dirname(os.path.abspath(__file__))
sols = np.load(os.path.join(HERE, "all-solutions.npy"))

def f(t):  return t**7 - 14*t**5 + 49*t**3 - 36*t + 1
def fp(t): return 7*t**6 - 70*t**4 + 147*t**2 - 36

def high_roots(dps):
    mp.mp.dps = dps + 40
    seedr = np.roots([1,0,-14,0,49,0,-36,1]).real
    rts=[]
    for x0 in seedr:
        x=mp.mpf(repr(float(x0)))
        for _ in range(400):
            dx=f(x)/fp(x); x=x-dx
            if abs(dx)<mp.mpf(10)**(-(dps+20)): break
        rts.append(x)
    return sorted(rts)

def residual(z, rts):
    a,b,c,p,q,rr,D = z; out=[]
    for t in rts:
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr
        out.append(u*u*(up*up+vq*vq)-D*vq*vq)
    return mp.matrix(out)

def jacobian(z, rts):
    a,b,c,p,q,rr,D=z; J=mp.zeros(7,7)
    for i,t in enumerate(rts):
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vq=p*t**2+q*t+rr; S=up*up+vq*vq
        J[i,0]=2*u*t*t*S+u*u*(4*up*t); J[i,1]=2*u*t*S+u*u*(2*up); J[i,2]=2*u*S
        J[i,3]=2*(u*u-D)*vq*t*t; J[i,4]=2*(u*u-D)*vq*t; J[i,5]=2*(u*u-D)*vq; J[i,6]=-vq*vq
    return J

def refine(z, dps):
    mp.mp.dps=dps+60; rts=high_roots(dps+60)
    z=[mp.mpf(x) for x in z]; nrm=mp.mpf(1)
    for it in range(150):
        F=residual(z,rts); nrm=max(abs(v) for v in F)
        if nrm<mp.mpf(10)**(-(dps+30)): break
        dz=mp.lu_solve(jacobian(z,rts),F); z=[z[k]-dz[k] for k in range(7)]
    return z,nrm

def deg_of(x,dps,maxdeg,steps=3000):
    for d in range(1,maxdeg+1):
        maxc=10**(dps//(2*(d+1)))
        rel=mp.pslq([x**j for j in range(d+1)], tol=mp.mpf(10)**(-(dps*3//4)),
                    maxcoeff=maxc, maxsteps=steps)
        if rel:
            H=max(abs(int(v)) for v in rel)
            val=abs(sum(int(c)*x**j for j,c in enumerate(rel)))
            if (d+1)*mp.log10(H)<=mp.mpf(dps)/2 and val<mp.mpf(10)**(-(dps*2//3)):
                return (d,H,val)
    return None

DPS=int(sys.argv[1]) if len(sys.argv)>1 else 700
MAXD=int(sys.argv[2]) if len(sys.argv)>2 else 8
seen=[]
print("screening Delta, dps=%d maxdeg=%d" % (DPS,MAXD))
for si,s in enumerate(sols):
    z,nrm=refine(s,DPS)
    D=z[6]
    # skip duplicates of already-tested Delta
    if any(abs(D-y[6])<mp.mpf(10)**(-(DPS-20)) for y in seen):
        continue
    seen.append(z)
    t=time.time()
    r=deg_of(D,DPS,MAXD)
    tag = ("deg=%d log10H=%.1f"%(r[0],float(mp.log10(r[1])))) if r else ("no relation d<=%d"%MAXD)
    print("sol %2d  Delta=%s  ->  %s   (%.1fs)" % (si, mp.nstr(D,18), tag, time.time()-t), flush=True)
print("distinct Delta tested:", len(seen))
