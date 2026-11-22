# Session 23: degree of Y (nonics dividing a fact 6 decic, cone in P^8) by monodromy.
# Unknowns x = (u, w, t0, y0, y1, y2, s0, s1, s2, d), y3 = 1.
# Equations: coeffs t^0..t^9 of y^2 y'^2 + (y^2-d^2) s^2 - 9 (t-t0) prod(t - z0 - u z1 - w z2).
import numpy as np, sys, pickle
P=np.polynomial.polynomial
rng=np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def crand(*sh): return rng.normal(size=sh)+1j*rng.normal(size=sh)
def pad(c,n=11):
    out=np.zeros(n,complex); out[:len(c)]=c; return out
def system(x,Z):
    z0,z1,z2=Z
    u,w,t0,y0,y1,y2,s0,s1,s2,d=x
    y=np.array([y0,y1,y2,1]); s=np.array([s0,s1,s2])
    yp=P.polyder(y); ysq=P.polymul(y,y)
    F=P.polyadd(P.polymul(ysq,P.polymul(yp,yp)),P.polymul(P.polysub(ysq,[d*d]),P.polymul(s,s)))
    z=z0+u*z1+w*z2
    M=P.polyfromroots(z)
    kap=9+s2*s2
    R=kap*P.polymul([-t0,1],M)
    E=pad(F)-pad(R)
    # Jacobian
    J=np.zeros((11,10),complex)
    for j in range(9):
        Mj=P.polyfromroots(np.delete(z,j))
        dRdz=-kap*P.polymul([-t0,1],Mj)
        J[:,0]-=pad(dRdz)*z1[j]; J[:,1]-=pad(dRdz)*z2[j]
    J[:,2]=pad(kap*M)
    for i in range(3):
        ti=np.zeros(i+1,complex); ti[i]=1
        dyi=P.polyder(ti) if i>0 else np.zeros(1)
        dF=2*P.polymul(P.polymul(y,P.polymul(yp,yp)),ti)+2*P.polymul(P.polymul(ysq,yp),dyi)+2*P.polymul(P.polymul(y,P.polymul(s,s)),ti)
        J[:,3+i]=pad(dF)
        J[:,6+i]=pad(2*P.polymul(P.polysub(ysq,[d*d]),P.polymul(s,ti)))
    J[:,9]=pad(-2*d*P.polymul(s,s))
    J[:,8]-=pad(2*s2*P.polymul([-t0,1],M))
    return E[:10],J[:10]   # t^10 coefficient cancels identically
def newton(x,Z,it=8,tol=1e-11):
    for _ in range(it):
        E,J=system(x,Z)
        dx=np.linalg.solve(J,-E); x=x+dx
        if np.linalg.norm(dx)<tol*(1+np.linalg.norm(x)): return x,True
    return x,np.linalg.norm(dx)<1e-7*(1+np.linalg.norm(x))
def dZ(ZA,ZB): return [b-a for a,b in zip(ZA,ZB)]
def track(x,ZA,ZB):
    # straight segment ZA->ZB
    tau=0.0; h=0.05; D=dZ(ZA,ZB)
    while tau<1:
        h=min(h,1-tau)
        Zc=[a+tau*dd for a,dd in zip(ZA,D)]
        E,J=system(x,Zc)
        # dx/dtau = -J^{-1} dE/dtau, dE/dtau via finite difference in Z
        Zn=[a+(tau+1e-6)*dd for a,dd in zip(ZA,D)]
        E2,_=system(x,Zn); dEdt=(E2-E)/1e-6
        v=np.linalg.solve(J,-dEdt)
        xp=x+h*v
        Zt=[a+(tau+h)*dd for a,dd in zip(ZA,D)]
        xn,ok=newton(xp,Zt,it=5,tol=1e-9)
        if ok and np.linalg.norm(xn-xp)<0.1*(1+np.linalg.norm(x)):
            x=xn; tau+=h; h=min(h*1.5,0.1)
        else:
            h/=2
            if h<1e-7: return None
    x,ok=newton(x,ZB,it=10)
    return x if ok else None
def key(x):
    # (u,w) identifies the point of Y on the plane; t0 distinguishes fibres
    return (round(x[0].real,6),round(x[0].imag,6),round(x[1].real,6),round(x[1].imag,6),round(x[2].real,5),round(x[2].imag,5))
# start point
while True:
    y=np.append(crand(3),1); s=crand(3); d=crand(1)[0]
    yp=P.polyder(y)
    F=P.polyadd(P.polymul(P.polymul(y,y),P.polymul(yp,yp)),P.polymul(P.polysub(P.polymul(y,y),[d*d]),P.polymul(s,s)))
    rts=P.polyroots(F)
    if len(rts)==10: break
t0=rts[0]; zs=rts[1:]
z1,z2=crand(9),crand(9)
Z0=[zs.copy(),z1,z2]
x0=np.array([0,0,t0,y[0],y[1],y[2],s[0],s[1],s[2],d],complex)
x0,ok=newton(x0,Z0); assert ok
sols={key(x0):x0}
stable=0; loops=0
while stable<int(sys.argv[2]) if len(sys.argv)>2 else 6:
    ZB=[crand(9),crand(9),crand(9)]; ZC=[crand(9),crand(9),crand(9)]
    new=0
    for k,x in list(sols.items()):
        xa=track(x,Z0,ZB)
        if xa is None: continue
        xb=track(xa,ZB,ZC)
        if xb is None: continue
        xc=track(xb,ZC,Z0)
        if xc is None: continue
        kk=key(xc)
        if kk not in sols: sols[kk]=xc; new+=1
    loops+=1
    pts=len({k[:4] for k in sols})
    print(f"loop {loops}: {len(sols)} solutions (sign-reduced not applied), {pts} distinct (u,w)",flush=True)
    stable = stable+1 if new==0 else 0
pickle.dump((Z0,sols),open(f"ydeg_{sys.argv[1] if len(sys.argv)>1 else 1}.pkl","wb"))
