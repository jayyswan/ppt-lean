import numpy as np, sys
from hilb import *
sys.argv=['x','0','0']
exec(open('linepairs.py').read().split('good, stats')[0])
x0=np.load('pairs_1.npy')[0]
E=np.stack([x0[:9],x0[9:18],x0[18:]],1); q=np.zeros(6); q[IDX[2][(0,1,1)]]=1.0
l3,h3,_,_=fit_lh(E,q); u0=np.concatenate([E.ravel(),q,l3,h3])
Jm=jac(u0); U,s,Vt=np.linalg.svd(Jm); K=Vt[33:]; c=U[:,33]; h=1e-3
def D2(v,w): return c@(F(u0+h*v+h*w)-F(u0+h*v-h*w)-F(u0-h*v+h*w)+F(u0-h*v-h*w))/(4*h*h)
Q=np.array([[D2(K[i],K[j]) for j in range(13)] for i in range(13)]); Q=(Q+Q.T)/2
w,V=np.linalg.eigh(Q); i1,i2=np.argmax(w),np.argmin(w)
vp,vm=V[:,i1]*np.sqrt(-w[i2]),V[:,i2]*np.sqrt(w[i1])   # Q(vp+-vm)=0
def qmat(qq):
    e=M[2]; A=np.zeros((3,3))
    for k,ex in enumerate(e):
        idx=[i for i in range(3) for _ in range(ex[i])]
        if idx[0]==idx[1]: A[idx[0],idx[0]]+=qq[k]
        else: A[idx[0],idx[1]]+=qq[k]/2; A[idx[1],idx[0]]+=qq[k]/2
    return A
def project(u):
    for it in range(30):
        Fu=F(u); 
        if np.linalg.norm(Fu)<1e-14: break
        u=u-np.linalg.lstsq(jac(u),Fu,rcond=None)[0]
    return u,np.linalg.norm(F(u))
for name,dirn in (('sheet+',K.T@(vp+vm)),('sheet-',K.T@(vp-vm))):
    dirn/=np.linalg.norm(dirn)
    out=[]
    for eps in (1e-2,5e-3,2.5e-3,1.25e-3):
        u,r=project(u0+eps*dirn)
        Em=u[:27].reshape(9,3); A=qmat(u[27:33])
        # normalise: det of conic matrix in an orthonormal frame of the plane, q scaled to unit norm
        Qf,Rf=np.linalg.qr(Em); B=np.linalg.inv(Rf).T@A@np.linalg.inv(Rf)
        B/=np.linalg.norm(B); out.append((eps,r,abs(np.linalg.det(B))))
    print(name,' '.join('eps=%.4f res=%.0e det=%.3e'%o for o in out))
    print('   det ratios per halving:',[out[k][2]/out[k+1][2] for k in range(len(out)-1)])
