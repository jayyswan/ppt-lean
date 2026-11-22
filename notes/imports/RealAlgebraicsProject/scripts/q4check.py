# Session 36: 50-digit verification of rows of an arc file (rows: s, j, nQ4, relgap, x_1..x_9 sorted) at fixed L:
# Newton polish of the equal-potential system, line z_i=(1+s x_i)/y_i, p1,p3,p5 relative sizes, p7, and real roots of Q4|line.
# usage: python3 q4check.py arc_3.60_-1.npy <L> <beta targets comma>
import sys, numpy as np, mpmath as mp
mp.mp.dps=50
o=np.load(sys.argv[1]); L=mp.mpf(sys.argv[2])
for bt in [float(b) for b in sys.argv[3].split(',')]:
    i=np.argmin(np.abs(o[:,0]-np.log(bt))); b=mp.mpf(np.exp(o[i,0])); X=mp.matrix([mp.mpf(v) for v in o[i,4:13]])
    h=lambda v:(v+1)*(v*v+b*b)
    for _ in range(25):
        R=mp.matrix(9,1); J=mp.matrix(9,9)
        for a in range(9):
            R[a]=mp.fsum([mp.log(abs(X[a]-X[c])) for c in range(9) if c!=a])-mp.mpf(2.5)*mp.log(h(X[a]))-L
            for c in range(9):
                if c!=a: J[a,c]=-1/(X[a]-X[c])
            J[a,a]=mp.fsum([1/(X[a]-X[c]) for c in range(9) if c!=a])-mp.mpf(2.5)*(1/(X[a]+1)+2*X[a]/(X[a]**2+b*b))
        X=X-mp.lu_solve(J,R)
    res=max(abs(R[a]) for a in range(9))
    Fp=[mp.fprod([X[a]-X[c] for c in range(9) if c!=a]) for a in range(9)]
    y=[mp.sign(Fp[a])*mp.sqrt(h(X[a])) for a in range(9)]
    Z=[1/v for v in y]; A=[X[a]/y[a] for a in range(9)]
    sc=max(max(abs(v) for v in Z),max(abs(v) for v in A)); Z=[v/sc for v in Z]; A=[v/sc for v in A]
    pk=lambda m:max(abs(mp.fsum([Z[a]**(m-k)*A[a]**k for a in range(9)])) for k in range(m+1))
    def ps(k): return [mp.binomial(k,j)*mp.fsum([Z[a]**(k-j)*A[a]**j for a in range(9)]) for j in range(k+1)]
    p2=ps(2); p4=ps(4); q=[6*p4[j] for j in range(5)]
    for a_ in range(3):
        for c_ in range(3): q[a_+c_]-=p2[a_]*p2[c_]
    rts=mp.polyroots(q[::-1],maxsteps=200,extraprec=100)
    nre=sum(1 for r in rts if abs(mp.im(r))<mp.mpf(10)**-30)
    print("beta=%.4g residual %.1e  p1 %.1e p3 %.1e p5 %.1e p7 %.2e  Q4|line real roots: %d  %s"%(float(b),float(res),float(pk(1)),float(pk(3)),float(pk(5)),float(pk(7)),nre,[mp.nstr(r,6) for r in rts if abs(mp.im(r))<1e-30]))
