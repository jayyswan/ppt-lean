import sys, random
from tb_core import *
import numpy as np
from scipy.optimize import least_squares
mp.mp.dps=40
_,R=q3_roots()
G=gammaQ_model([(b,2*b**2+b**4) for b in R])
A1,B1=G['W'].A,G['W'].B; j1=jinv(A1,B1)

def u_roots(r):
    # scan u>r^2 for j(D(r,u))=j1 with lambda^2>0
    out=[]; f=lambda u: jinv(D_model(r,u).A,D_model(r,u).B)-j1
    us=[r**2+mp.mpf(10)**e for e in np.linspace(-6,4,4001)]
    vals=[f(u) for u in us]
    for i in range(len(us)-1):
        if mp.sign(vals[i])!=mp.sign(vals[i+1]) and abs(vals[i])<1e7 and abs(vals[i+1])<1e7:
            try: u=mp.findroot(f,(us[i],us[i+1]),solver='anderson')
            except Exception: continue
            W2=D_model(r,u); lam2=W2.B*A1/(B1*W2.A)
            if lam2>0: out.append(u)
    return out

class Setup:
    def __init__(s,r,u,lsign=1):
        s.r,s.u=r,u; s.W2=D_model(r,u); lam=lsign*mp.sqrt(s.W2.B*A1/(B1*s.W2.A))
        s.E=[(lam**2*X,lam**3*Y) for (X,Y) in G['pts']]
        s.A2=chol_A2(r,u)
        for (X,Y) in s.E: assert abs(Y**2-X**3-s.W2.A*X-s.W2.B)<1e-25*(1+abs(Y)**2)
    def P2s(s,d1,d2,tT,ssg=1,gsg=1):
        mu,w=D_point_from_t(tT,s.r,s.u,ssg,gsg)
        T=s.W2.to_short(mu,w)
        out=[]
        for e in s.E:
            X,Y=eadd(e,T,s.W2.A); m,ww=s.W2.from_short(X,Y)
            t,s1,sig=mu_to_tower(m,ww)
            out.append(tower_P2(t,s1,sig,d1,d2,s.A2))
        return out

def residual(S,z,sg):
    d1,d2,tT,xs,ys=[mp.mpf(v) for v in z]
    P=S.P2s(d1,d2,tT,*sg)
    mx=sum(p[0] for p in P)/9; my=sum(p[1] for p in P)/9
    sc=mp.sqrt(sum((p[0]-mx)**2+(p[1]-my)**2 for p in P)/9)
    Pn=[((p[0]-mx)/sc,(p[1]-my)/sc) for p in P]
    c,Sv=cubic_through(Pn)
    a,b,cc,d=c[6],c[7]/3,c[8]/3,c[9]
    H=[a*cc-b**2,a*d-b*cc,b*d-cc**2]
    fx,fy=Fgrad(c,xs,ys)
    return [float(v) for v in H+[Feval(c,xs,ys),fx,fy]], Pn, c, Sv

if __name__=='__main__':
    r=mp.mpf(sys.argv[1]); seed=int(sys.argv[2]); nst=int(sys.argv[3])
    us=u_roots(r); print('r=',r,'u roots',[mp.nstr(u,12) for u in us]); sys.stdout.flush()
    rng=np.random.default_rng(seed); sols=[]
    for u in us:
      for lsg in (1,-1):
        S=Setup(r,u,lsg)
        for sg in [(1,1),(1,-1),(-1,1),(-1,-1)]:
          for k in range(nst):
            z0=np.concatenate([rng.normal(0,3,2),rng.normal(0,2,1),rng.normal(0,1.5,2)])
            try:
                res=least_squares(lambda z: residual(S,z,sg)[0], z0, method='lm', xtol=1e-14, ftol=1e-14, max_nfev=400)
            except Exception as ex: continue
            if res.cost<1e-18:
                _,Pn,c,Sv=residual(S,res.x,sg)
                gap=float(Sv[Sv.rows-2]/Sv[0]); dmin=min(float(mp.sqrt((Pn[i][0]-Pn[j][0])**2+(Pn[i][1]-Pn[j][1])**2)) for i in range(9) for j in range(i))
                dsing=min(float(mp.sqrt((p[0]-res.x[3])**2+(p[1]-res.x[4])**2)) for p in Pn)
                if gap<1e-4 or dmin<1e-3 or dsing<1e-3:
                    print('  degenerate (gap %.1e, dmin %.1e, dsing %.1e)'%(gap,dmin,dsing)); continue
                Jr=np.linalg.svd(res.jac,compute_uv=False)
                print('SOL u=%s lsg=%d sg=%s z=%s cost=%.1e jac_sv=%s'%(mp.nstr(u,8),lsg,sg,np.array2string(res.x,precision=6),res.cost,np.array2string(Jr,precision=2)))
                sys.stdout.flush(); sols.append((u,lsg,sg,res.x))
    print('done, %d solutions'%len(sols))
