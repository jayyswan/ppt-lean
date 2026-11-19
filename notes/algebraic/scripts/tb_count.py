import sys, pickle
from tb_cplx import *
r=float(sys.argv[1]); seed=int(sys.argv[2]); N=int(sys.argv[3])
sy=Sys(r); rng=np.random.default_rng(seed)
shift=(0.5511496005440762,14.818190054530863); scale=15.0
def newton(z):
    for it in range(80):
        f,c=sy.F(z,shift,scale)
        h=1e-7*(1+np.abs(z))
        J=np.empty((7,7),complex)
        for k in range(7):
            zz=z.copy(); zz[k]+=h[k]; J[:,k]=(sy.F(zz,shift,scale)[0]-f)/h[k]
        try: dz=np.linalg.solve(J,-f)
        except np.linalg.LinAlgError: return None
        lam=1.0 if it>10 else 0.5
        z=z+lam*dz
        if not np.all(np.isfinite(z)) or np.max(np.abs(z))>1e6: return None
        if np.linalg.norm(dz)<1e-9*(1+np.linalg.norm(z)): 
            f,c=sy.F(z,shift,scale); return z,c,np.linalg.cond(J)
    return None
sols=[]
def key(z): return z[:4]
for k in range(N):
    tT=rng.normal(0,1.5)+1j*rng.normal(0,1.5)
    s1=np.sqrt(4*tT**2+1); mu=s1-2*tT; sig=np.sqrt(4*tT**2-4*complex(sy.S.r)*tT+complex(sy.S.u)); w=sig*mu
    # map to short Weierstrass via mp
    XT,YT=sy.S.W2.to_short(mp.mpc(mu),mp.mpc(w)); 
    z0=np.array([complex(*rng.normal(0,3,2)),complex(*rng.normal(0,3,2)),complex(XT),complex(YT),complex(*rng.normal(0,0.5,2)),complex(*rng.normal(0,0.5,2)),complex(*rng.normal(0,1,2))])
    out=newton(z0)
    if out is None: continue
    z,c,cond=out
    H1=0.0; cp=1.0
    P2=sy.P2(*z[:4]); pts=np.array([(P2[0]-shift[0])/scale,(P2[1]-shift[1])/scale]).T
    dmin=min(np.abs(pts[i]-pts[j]).max() for i in range(9) for j in range(i))
    dsing=np.min(np.abs(pts-z[4:6]).max(axis=1))
    good = H1<1e-6 and dmin>1e-6 and dsing>1e-6 and cond<1e12
    if not good: continue
    if all(np.max(np.abs(key(z)-key(s)))>1e-6*(1+np.max(np.abs(key(s)))) for s in sols):
        sols.append(z)
    if (k+1)%200==0: print(k+1,'distinct',len(sols),flush=True)
print('final distinct',len(sols)); pickle.dump(sols,open('cnt_%s_%d.pkl'%(sys.argv[1],seed),'wb'))
nreal=sum(1 for z in sols if np.max(np.abs(z.imag))<1e-6); print('real',nreal)
