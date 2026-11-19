from tb_solve import *
mp.mp.dps=50
def cvec(r,u_index,d1,d2,tT,lsg=1,sg=(1,1)):
    u=u_roots(r)[u_index]; S=Setup(r,u,lsg)
    P=S.P2s(d1,d2,tT,*sg)
    c,_=cubic_through(P)
    c=mp.matrix(c); 
    k=max(range(10),key=lambda i:abs(c[i])); return c/c[k]   # affine chart on P^9
import random
for trial,(r0,d1,d2,tT) in enumerate([(0.2,0.7,-0.4,0.3),(0.35,-1.1,0.8,-0.6),(0.1,0.5,1.5,1.2)]):
    base=[mp.mpf(v) for v in (r0,d1,d2,tT)]
    f=lambda v: cvec(v[0],0,v[1],v[2],v[3])
    c0=f(base); h=mp.mpf(10)**-15
    cols=[]
    for i in range(4):
        vp=list(base); vp[i]+=h; vm=list(base); vm[i]-=h
        cols.append((f(vp)-f(vm))/(2*h))
    J=mp.matrix(10,4)
    for i in range(4):
        for k in range(10): J[k,i]=cols[i][k]
    print(trial,'sing vals of d(cubic)/d(r,d1,d2,T):',[mp.nstr(s,4) for s in mp.svd_r(J,compute_uv=False)])
