# Analytic (rational) form of the fibre system for complex solution counting.
# unknowns z = (d1, d2, XT, YT, xs, ys); r fixed, u slaved, Q fixed.
import numpy as np, mpmath as mp
from tb_solve import u_roots, Setup, A1, B1
from tb_core import MONS
mp.mp.dps=40
class Sys:
    def __init__(s, r, ui=0, lsg=1):
        u=u_roots(mp.mpf(r))[ui]; S=Setup(mp.mpf(r),u,lsg); s.S=S
        W=S.W2; s.A=complex(W.A); s.Bc=complex(W.B)
        a1,a2,a3,a4,a6=W.ai; s.a1,s.a3=complex(a1),complex(a3); s.b2=complex(W.b2)
        s.q,s.c,s.d=complex(W.q),complex(W.c),complex(W.d)
        s.E=np.array([[complex(X),complex(Y)] for X,Y in S.E])
        A2=S.A2; s.A2=np.array([[complex(A2[i,j]) for j in range(2)] for i in range(2)])
        s.A2iT=np.linalg.inv(s.A2).T
        s.mono=np.array(MONS)
    def P2(s,d1,d2,XT,YT):
        x1,y1=s.E[:,0],s.E[:,1]
        l=(YT-y1)/(XT-x1); X3=l*l-x1-XT; Y3=l*(x1-X3)-y1
        x=X3-s.b2/12; y=Y3-(s.a1*x+s.a3)/2
        mu=(2*s.q*(x+s.c)-s.d**2/(2*s.q))/y; w=-s.q+mu*(mu*x-s.d)/(2*s.q)
        t=(1/mu-mu)/4; s1=(mu+1/mu)/2; sig=w/mu
        N0=np.array([-2*t,np.ones_like(t)]); P0=np.array([t,t*t])
        P1=P0+d1*N0/s1
        P2=s.A2@P1+d2*(s.A2iT@N0)/sig
        return P2
    def cubic(s,P2,shift):
        X=P2[0]-shift[0]; Y=P2[1]-shift[1]
        M=np.array([X**i*Y**j for (i,j) in MONS]).T   # 9x10
        return np.array([(-1)**k*np.linalg.det(np.delete(M,k,axis=1)) for k in range(10)])
    def F(s,z,shift,scale):
        d1,d2,XT,YT,xs,ys,m=z
        P2=s.P2(d1,d2,XT,YT)
        P2=np.array([(P2[0]-shift[0])/scale,(P2[1]-shift[1])/scale])
        c=s.cubic(P2,(0,0)); c=c/c[6]
        a,b,cc,d=c[6],c[7]/3,c[8]/3,c[9]
        fx=sum(c[k]*i*xs**(i-1)*ys**j for k,(i,j) in enumerate(MONS) if i>0)
        fy=sum(c[k]*j*xs**i*ys**(j-1) for k,(i,j) in enumerate(MONS) if j>0)
        f=sum(c[k]*xs**i*ys**j for k,(i,j) in enumerate(MONS))
        return np.array([YT**2-XT**3-s.A*XT-s.Bc, b-a*m, cc-a*m*m, d-a*m**3, f, fx, fy]), c
