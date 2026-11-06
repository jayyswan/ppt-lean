# Phase 0: honest degree of Delta by PSLQ at very high precision, searching degree up to MAXD.
import mpmath as mp, numpy as np, sys, os, json
sys.stdout.reconfigure(line_buffering=True)
HERE = os.path.dirname(os.path.abspath(__file__))

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

def residual(z,rts):
    a,b,c,p,q,rr,D=z; out=[]
    for t in rts:
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vp=2*p*t+q; vv=p*t**2+q*t+rr
        out.append(u*u*(up*up+vp*vp)-D*vv*vv)
    return mp.matrix(out)

def jacobian(z,rts):
    a,b,c,p,q,rr,D=z; J=mp.zeros(7,7)
    for i,t in enumerate(rts):
        u=t**3+a*t**2+b*t+c; up=3*t**2+2*a*t+b; vp=2*p*t+q; vv=p*t**2+q*t+rr; S=up*up+vp*vp
        J[i,0]=2*u*t*t*S+u*u*(4*up*t); J[i,1]=2*u*t*S+u*u*(2*up); J[i,2]=2*u*S
        J[i,3]=u*u*(4*vp*t)-D*(2*vv*t*t); J[i,4]=u*u*(2*vp)-D*(2*vv*t)
        J[i,5]=-D*(2*vv); J[i,6]=-vv*vv
    return J

def refine(z,dps):
    mp.mp.dps=dps+60; rts=high_roots(dps+60)
    z=[mp.mpf(x) for x in z]; nrm=mp.mpf(1)
    for it in range(150):
        F=residual(z,rts); nrm=max(abs(v) for v in F)
        if nrm<mp.mpf(10)**(-(dps+30)): break
        dz=mp.lu_solve(jacobian(z,rts),F); z=[z[k]-dz[k] for k in range(7)]
    return z,nrm

def deg_of(x,dps,maxdeg):
    for d in range(1,maxdeg+1):
        maxc=10**(dps//(2*(d+1)))
        rel=mp.pslq([x**j for j in range(d+1)],tol=mp.mpf(10)**(-(dps*3//4)),
                    maxcoeff=maxc,maxsteps=10**7)
        if rel:
            H=max(abs(int(v)) for v in rel)
            val=abs(sum(int(c)*x**j for j,c in enumerate(rel)))
            if (d+1)*mp.log10(H)<=mp.mpf(dps)/2 and val<mp.mpf(10)**(-(dps*2//3)):
                return d,H,val,[int(v) for v in rel]
    return None

DPS=int(sys.argv[1]) if len(sys.argv)>1 else 2500
MAXD=int(sys.argv[2]) if len(sys.argv)>2 else 24
sols=np.load(os.path.join(HERE,"all-solutions.npy"))
si=int(sys.argv[3]) if len(sys.argv)>3 else 0
z,nrm=refine(sols[si],DPS)
print("solution",si,"max|F|=",mp.nstr(nrm,4),flush=True)
print("Delta=",mp.nstr(z[6],40),flush=True)
res=deg_of(z[6],DPS,MAXD)
print("Delta degree:",res,flush=True)
