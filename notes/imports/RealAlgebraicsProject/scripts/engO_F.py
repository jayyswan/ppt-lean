# Session 38: Engine O, full F_{h,u} for h = x^3+a x+b, u = e1(F)-c^2.
# Newton continuation in (a,b,U) from the S37.3 example; prints exact e_k*B(u).
# usage: python3 engO_F.py <npts> <seed>   writes engO_pts.txt (a b u c2 e1..e9 as rationals)
import sys, random, mpmath as mp, cypari
P=cypari.pari; mp.mp.dps=70
def Af(u,a,b): return u**6+1278*a*u**4+50274*b*u**3+3321*a**2*u**2+2357586*a*b*u-1822500*a**3+6751269*b**2
def Bf(u,a,b): return u**5+1296*a*u**3+50112*b*u**2+27648*a**2*u+2985984*a*b
def rem(F,G):   # F monic coeff list high->low (len 10), G list high->low; remainder of G mod F, low part len 9
    G=list(G)
    for i in range(len(G)-len(F)+1):
        q=G[i]
        if q!=0:
            for j in range(len(F)): G[i+j]-=q*F[j]
    return G[-(len(F)-1):]
def pmul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]+=x*y
    return r
def resid(v,a,b,u):  # v = [e2..e9, c2]
    c2=v[8]; e1=c2+u
    e=[1,e1]+list(v[:8]); F=[(-1)**k*e[k] for k in range(10)]
    dF=[F[k]*(9-k) for k in range(9)]
    h=[1,0,a,b]; h5=[1]
    for _ in range(5): h5=pmul(h5,h)
    G=pmul(dF,dF); G=[G[i]-c2*h5[i-1] if i>=1 else G[i] for i in range(len(G))]
    return rem(F,G)
def newton(v,a,b,u,it=30,tol=None):
    tol=tol or mp.mpf(10)**(-mp.mp.dps+8)
    for k in range(it):
        r=resid(v,a,b,u); nr=max(abs(x) for x in r)/(1+max(abs(x) for x in v))**2
        if nr<tol: return v,nr
        J=mp.matrix(9,9); eps=mp.mpf(10)**(-mp.mp.dps//2)
        for j in range(9):
            w=list(v); w[j]+=eps; rj=resid(w,a,b,u)
            for i in range(9): J[i,j]=(rj[i]-r[i])/eps
        d=mp.lu_solve(J,mp.matrix(r))
        v=[v[i]-d[i] for i in range(9)]
    return v,nr
# start: S37.3 example shifted x = X - 1/3
Fx=P('(4184*x^9+10775*x^8-21954*x^7-255050*x^6-730124*x^5-1093620*x^4-944440*x^3-446680*x^2-81360*x+4320)/4184')
FX=P(f'subst({Fx},x,X-1/3)')
co=[P(f'polcoef({FX},{9-k},X)') for k in range(10)]
e=[mp.mpf(int(P(f"numerator({c})")))/int(P(f"denominator({c})"))*(-1)**k for k,c in enumerate(co)]
a0,b0,u0=mp.mpf(5)/3,mp.mpf(38)/27,mp.mpf(-22)
c20=mp.mpf(93825)/4184
print('check c2 formula', -Af(u0,a0,b0)/Bf(u0,a0,b0)-c20, ' e1-c2-u', e[1]-c20-u0)
v=e[2:]+[c20]; v,nr=newton(v,a0,b0,u0); print('start resid',mp.nstr(nr,3))
def go(v,p0,p1,steps):
    t=mp.mpf(0); dt=mp.mpf(1)/steps; prev=None; vt=[mp.mpc(x) for x in v]
    while t<1:
        dt=min(dt,1-t); tn=t+dt; p=[p0[i]+tn*(p1[i]-p0[i]) for i in range(3)]
        guess=vt if prev is None else [vt[i]+(vt[i]-prev[0][i])*dt/prev[1] for i in range(9)]
        mp.mp.dps=30; vv,nr=newton(guess,*p,it=8); mp.mp.dps=70
        ok = nr<1e-18 and max(abs(vv[i]-guess[i])/(1+abs(vt[i])) for i in range(9))<0.1
        if ok:
            prev=(vt,dt); vt=vv; t=tn; dt*=2
        else:
            dt/=2.5
            if dt<1e-7: return None
    v,nr=newton(vt,*p1); return v if nr<1e-45 else None
def rat(z): return P(f'bestappr({mp.nstr(mp.re(z),65)},10^25)')
npts=int(sys.argv[1]); random.seed(int(sys.argv[2]))
out=open(sys.argv[3] if len(sys.argv)>3 else 'engO_pts.txt','w'); cur=v; p=[a0,b0,u0]; got=0; tries=0
while got<npts and tries<5*npts:
    tries+=1
    q=[mp.mpf(random.randint(-6,6)),mp.mpf(random.randint(-6,6)),mp.mpf(random.randint(-40,40))]
    if Bf(*[q[2],q[0],q[1]])==0: continue
    # complex detour midpoint to avoid real branch points
    mid=[(p[i]+q[i])/2+mp.mpc(0,random.uniform(-2,2)) for i in range(3)]
    w=go(cur,p,mid,60); w=go(w,mid,q,60) if w else None
    if not w: print('fail',q); continue
    cur=w; p=q; got+=1
    c2=w[8]; e1=c2+q[2]
    vals=[rat(x) for x in [c2,e1]+list(w[:8])]
    imag=max(abs(mp.im(x)) for x in w)
    chk=P(f'{vals[0]}+({Af(q[2],q[0],q[1])})/({Bf(q[2],q[0],q[1])})')
    print(int(q[0]),int(q[1]),int(q[2]),'imag',mp.nstr(imag,3),'c2 formula chk',chk, flush=True)
    out.write(' '.join([str(int(q[0])),str(int(q[1])),str(int(q[2]))]+[str(x) for x in vals])+'\n'); out.flush()
