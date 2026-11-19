from tb_inspect import *
import sys
mp.mp.dps=60
def refine(r,ui,lsg,sg,z):
    u=u_roots(mp.mpf(r))[ui]; S=Setup(mp.mpf(r),u,lsg)
    def Fv(*zz):
        d1,d2,tT,xs,ys=zz
        P=S.P2s(d1,d2,tT,*sg)
        mx=sum(p[0] for p in P)/9; my=sum(p[1] for p in P)/9
        Pn=[(p[0]-mx,p[1]-my) for p in P]
        c,_=cubic_through(Pn); k=max(range(10),key=lambda i:abs(c[i])) if not hasattr(Fv,'k') else Fv.k
        Fv.k=k; c=[x/c[k] for x in c]
        a,b,cc,d=c[6],c[7]/3,c[8]/3,c[9]
        fx,fy=Fgrad(c,xs,ys)
        return [a*cc-b**2, b*d-cc**2, Feval(c,xs,ys), fx, fy]
    # convert singular point to centred (unnormalised) coords
    P=S.P2s(*[mp.mpf(v) for v in z[:3]],*sg); mx=sum(p[0] for p in P)/9; my=sum(p[1] for p in P)/9
    sc=mp.sqrt(sum((p[0]-mx)**2+(p[1]-my)**2 for p in P)/9)
    z0=[mp.mpf(z[0]),mp.mpf(z[1]),mp.mpf(z[2]),mp.mpf(z[3])*sc,mp.mpf(z[4])*sc]
    sol=mp.findroot(Fv,z0,tol=mp.mpf(10)**-50,maxsteps=50)
    print('refined:',[mp.nstr(x,30) for x in sol])
    print('residual',[mp.nstr(v,3) for v in Fv(*sol)])
    return S,sol
if __name__=='__main__':
    S,sol=refine(-0.5,0,1,(1,1),[4.80809,0.19608,-0.779941,-0.207165,0.104362])
    P=S.P2s(sol[0],sol[1],sol[2],1,1)
    print('P2 points:',[(mp.nstr(p[0],8),mp.nstr(p[1],8)) for p in P])
