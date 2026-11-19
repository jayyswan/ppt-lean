from tb_solve import *
import numpy as np
mp.mp.dps=40
def inspect(r,u,lsg,sg,z):
    u=min(u_roots(mp.mpf(r)),key=lambda x:abs(x-u)); S=Setup(mp.mpf(r),u,lsg)
    res,Pn,c,Sv=residual(S,z,sg)
    print('residual',np.array2string(np.array(res),precision=2))
    print('cubic coeffs',[mp.nstr(x,5) for x in c])
    print('|cubic part|',mp.nstr(mp.sqrt(sum(c[k]**2 for k in (6,7,8,9))),5),' smallest sv of 9x10:',mp.nstr(Sv[Sv.rows-1],4),mp.nstr(Sv[Sv.rows-2],4))
    xs,ys=z[3],z[4]; print('sing pt',xs,ys,' min dist to points',min(float(mp.sqrt((p[0]-xs)**2+(p[1]-ys)**2)) for p in Pn))
    # Hessian matrix at singular point -> node/cusp type
    h=mp.mpf(10)**-12
    def F(x,y): return Feval(c,x,y)
    fxx=(F(xs+h,ys)-2*F(xs,ys)+F(xs-h,ys))/h**2; fyy=(F(xs,ys+h)-2*F(xs,ys)+F(xs,ys-h))/h**2
    fxy=(F(xs+h,ys+h)-F(xs+h,ys-h)-F(xs-h,ys+h)+F(xs-h,ys-h))/(4*h*h)
    print('hess det at sing',mp.nstr(fxx*fyy-fxy**2,5),'(neg=crunode, pos=acnode, 0=cusp)')
    print('points',[(mp.nstr(p[0],5),mp.nstr(p[1],5)) for p in Pn])
    return S,c,Pn
if __name__=='__main__':
    import sys
    inspect(0,0.0279904130229067,1,(1,1),[-0.772504,0.375438,-2.135901,-0.003865,-0.388027])
