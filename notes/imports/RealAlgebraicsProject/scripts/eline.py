"""Session 27: E-lines. Find the central conic q(Z_i,a_i)=1, parametrise, and check the
quadrinomial X^9 + A X^7 + B X^2 + C description."""
import numpy as np, sys
np.set_printoptions(precision=6, suppress=True, linewidth=170)
X=np.load(sys.argv[1])
for x in X[:: max(1,len(X)//4)]:
    Z,a=x[:9],x[9:18]
    A=np.stack([np.ones(9),Z*Z,Z*a,a*a],1); k=np.linalg.svd(A)[2][-1]; k=-k/k[0]
    Qm=np.array([[k[1],k[2]/2],[k[2]/2,k[3]]])          # q(Z,a) = [Z a] Qm [Z a]^T = 1
    ev,V=np.linalg.eigh(Qm); print('q eigenvalues',ev, 'resid',np.abs(A[:,1:]@k[1:]-1).max())
    if ev[0]*ev[1]<0:
        # hyperbola: q = (u)(v) with u,v real linear forms: write q = ev0 p^2 + ev1 r^2
        p=V[:,0]; r=V[:,1]; c0=np.sqrt(-ev[0]); c1=np.sqrt(ev[1])
        u=c1*r+c0*p; v=c1*r-c0*p        # q = u*v ... check
        P2=np.stack([Z,a],1); lam=P2@u; mu=P2@v
        print('  hyperbola: lam*mu',np.round(lam*mu,8))
    else:
        s=np.sign(ev[0]); L=np.linalg.cholesky(s*Qm); P2=np.stack([Z,a],1)@L
        lam=P2[:,0]+1j*P2[:,1]; print('  ellipse (sign %d): |lam|'%s,np.round(abs(lam),8))
    c=np.poly(lam); c=c/c[0]
    print('  coeffs of prod(X-lam): ',np.round(c,7))
