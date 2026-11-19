# Export data + the known real solution for the polynomial (HC.jl) formulation, and verify residual/Jacobian.
import json, sys
from tb_refine import *
mp.mp.dps=60
r=mp.mpf(sys.argv[1]) if len(sys.argv)>1 else mp.mpf(-0.5)
S,sol=refine(-0.5,0,1,(1,1),[4.80809,0.19608,-0.779941,-0.207165,0.104362])
d1,d2,tT,xs,ys=sol
W=S.W2; a1,a2,a3,a4,a6=W.ai
mu,w=D_point_from_t(tT,S.r,S.u,1,1); XT,YT=W.to_short(mu,w)
A2=S.A2; A2iT=(A2.T)**-1
# per-point data
lam=[];mus=[];P2=[]
for (x,y) in S.E:
    l=(YT-y)/(XT-x); lam.append(l)
    X=l**2-x-XT; Y=l*(x-X)-y; xl=X-W.b2/12; yl=Y-(a1*xl+a3)/2
    m=(2*W.q*(xl+W.c)-W.d**2/(2*W.q))/yl; mus.append(m)
P=S.P2s(d1,d2,tT,1,1)
# Bezier through P (from tb_bezier logic): node + cube direction
mx=sum(p[0] for p in P)/9; my=sum(p[1] for p in P)/9
Pc=[(p[0]-mx,p[1]-my) for p in P]; c,_=cubic_through(Pc)
m0=-3*c[6]/c[7]
F=lambda x,y: Feval(c,x,y)
def Bm(tau):
    m=m0+1/tau; v1=F(xs+1,ys+m); v2=F(xs+2,ys+2*m); a=v2/4-v1; b=v1-a; s=-b/a; return (xs+s+mx, ys+m*s+my)
taus=[mp.mpf(k)/7+mp.mpf(1)/3 for k in range(4)]
V=mp.matrix([[t**e for e in range(4)] for t in taus])
cx=mp.lu_solve(V,mp.matrix([Bm(t)[0] for t in taus])); cy=mp.lu_solve(V,mp.matrix([Bm(t)[1] for t in taus]))
# reparam tau = al*s + de : x-leading 1, x-quadratic 0
al=cx[3]**(-mp.mpf(1)/3); de=-cx[2]/(3*cx[3])
def comp(co):
    # poly in s of co(al s + de)
    out=[mp.mpf(0)]*4
    for e in range(4):
        for k in range(e+1): out[k]+=co[e]*mp.binomial(e,k)*al**k*de**(e-k)
    return out
bx=comp(cx); by=comp(cy)
tau_s=[]
for (px,py) in Pc:
    m=(py-ys)/(px-xs); t=1/(m-m0); tau_s.append((t-de)/al)
print('bx',[mp.nstr(v,10) for v in bx]); print('by',[mp.nstr(v,10) for v in by])
data=dict(A=str(W.A),B=str(W.B),a1=str(a1),a3=str(a3),b2=str(W.b2),q=str(W.q),c=str(W.c),d=str(W.d),
  A2=[[str(A2[i,j]) for j in range(2)] for i in range(2)], A2iT=[[str(A2iT[i,j]) for j in range(2)] for i in range(2)],
  e=[[str(x),str(y)] for x,y in S.E])
z=dict(d1=d1,d2=d2,XT=XT,YT=YT,b0=bx[0],b1=bx[1],g0=by[0],g1=by[1],g2=by[2],g3=by[3])
sol_list=[d1,d2,XT,YT,bx[0],bx[1],by[0],by[1],by[2],by[3]]+lam+mus+tau_s
data['sol']=[str(v) for v in sol_list]
json.dump(data,open('tb_poly_data.json','w'),indent=0)
# residual of polynomial system
def system(v,dat=None):
    d1,d2,XT,YT,b0,b1,g0,g1,g2,g3=v[:10]; L=v[10:19]; M=v[19:28]; Tau=v[28:37]
    eqs=[YT**2-XT**3-W.A*XT-W.B]
    for i,(x,y) in enumerate(S.E):
        l,m,t=L[i],M[i],Tau[i]
        eqs.append(l*(XT-x)-(YT-y))
        X=l**2-x-XT; Y=l*(x-X)-y; xl=X-W.b2/12; yl=Y-(a1*xl+a3)/2
        eqs.append(m*yl-(2*W.q*(xl+W.c)-W.d**2/(2*W.q)))
        w=-W.q+m*(m*xl-W.d)/(2*W.q)
        Den=16*m**2*(1+m**2)*w
        P0D=(4*m*(1-m**2)*(1+m**2)*w, (1-m**2)**2*(1+m**2)*w)
        n1D=(-(1-m**2)*16*m**2*w, 32*m**3*w)
        Q1=(P0D[0]+d1*n1D[0], P0D[1]+d1*n1D[1])
        m2=(-(1-m**2)/2, m); k=16*m**2*(1+m**2)
        PD=[A2[j,0]*Q1[0]+A2[j,1]*Q1[1] + d2*k*(A2iT[j,0]*m2[0]+A2iT[j,1]*m2[1]) for j in range(2)]
        Bx=b0+b1*t+t**3; By=g0+g1*t+g2*t**2+g3*t**3
        eqs.append(PD[0]-Den*Bx); eqs.append(PD[1]-Den*By)
    return eqs
res=system(sol_list); print('max residual',mp.nstr(max(abs(e) for e in res),3))
h=mp.mpf(10)**-25
J=mp.matrix(37,37)
for k in range(37):
    vp=list(sol_list); vp[k]+=h; vm=list(sol_list); vm[k]-=h
    rp=system(vp); rm=system(vm)
    for i in range(37): J[i,k]=(rp[i]-rm[i])/(2*h)
sv=mp.svd_r(J,compute_uv=False); print('Jacobian sv min/max',mp.nstr(sv[36],4),mp.nstr(sv[0],4))
import numpy as np
Jn=np.array([[float(J[i,k]) for k in range(37)] for i in range(37)])
for _ in range(5):
    Jn=Jn/np.abs(Jn).max(axis=1,keepdims=True); Jn=Jn/np.abs(Jn).max(axis=0,keepdims=True)
print('equilibrated cond %.3e'%np.linalg.cond(Jn))
