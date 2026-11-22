# Session 36: trace the fold curve (boundary of the real S_ord region in the (L, beta) plane, one-component side)
# unknowns w = (x[9], s=log beta, L, v[9]); equations G(x,s,L)=0 (9), J_x v = 0 (9), c.v = 1 (1)  -> 19 eqs, 20 unknowns.
# start: last row of fold_<L>_<k>.npy (written by fold.py).  usage: python3 foldcurve.py fold_3.0_0.npy <L> <dir +1|-1> [steps]
import sys, numpy as np
rows=np.load(sys.argv[1]); L0=float(sys.argv[2]); dirn=float(sys.argv[3]); nsteps=int(sys.argv[4]) if len(sys.argv)>4 else 400
def G(x,s,L):
    b2=np.exp(2*s); d=x[:,None]-x[None,:]; np.fill_diagonal(d,1)
    return np.log(np.abs(d)).sum(1)-2.5*np.log((x+1)*(x*x+b2))-L
def Jx(x,s):
    b2=np.exp(2*s); d=x[:,None]-x[None,:]; np.fill_diagonal(d,1); iD=1/d; np.fill_diagonal(iD,0)
    J=-iD; np.fill_diagonal(J,iD.sum(1)-2.5*(1/(x+1)+2*x/(x*x+b2))); return J
def jinv(beta):
    e1,e2,e3=-1,1j*beta,-1j*beta; lam=(e3-e1)/(e2-e1); return (256*(lam*lam-lam+1)**3/(lam*lam*(lam-1)**2)).real
def q4real(x,s):
    b2=np.exp(2*s); h=(x+1)*(x*x+b2)
    Fp=np.array([np.prod([x[i]-x[j] for j in range(9) if j!=i]) for i in range(9)])
    y=np.sign(Fp)*np.sqrt(h); Z=1/y; A=x/y; Z/=np.abs(Z).max(); A/=np.abs(A).max()
    def ps(k):
        c=np.zeros(k+1)
        for i in range(9): c+=np.polynomial.polynomial.polypow([Z[i],A[i]],k)
        return c
    q=6*ps(4)-np.polynomial.polynomial.polymul(ps(2),ps(2))
    rts=np.roots(q[::-1]); return int(np.sum(np.abs(rts.imag)<1e-7*max(1,np.abs(rts).max())))
x=rows[-1,4:13].copy(); s=rows[-1,0]
J=Jx(x,s); v=np.linalg.svd(J)[2][-1]; c=v.copy()
def H(w):
    x,s,L,v=w[:9],w[9],w[10],w[11:]
    return np.concatenate([G(x,s,L), Jx(x,s)@v, [c@v-1]])
def DH(w):
    h=1e-7; f0=H(w); D=np.zeros((19,20))
    for k in range(20):
        dw=np.zeros(20); dw[k]=h*max(1e-3,abs(w[k])) if k<9 else h; D[:,k]=(H(w+dw)-f0)/dw[k]
    return D
w=np.concatenate([x,[s,L0],v/(c@v)])
# correct onto the fold at fixed L
for _ in range(30):
    f=H(w); D=DH(w); D=np.delete(D,10,axis=1); d=np.linalg.lstsq(D,f,rcond=None)[0]; d=np.insert(d,10,0.0); w=w-d
print("fold point at L=%.3f: beta=%.5g  |H|=%.1e"%(w[10],np.exp(w[9]),np.abs(H(w)).max()))
tprev=None; ds=0.02; out=[]
for st in range(nsteps):
    D=DH(w); t=np.linalg.svd(D)[2][-1]
    if tprev is None: t=t*np.sign(t[10])*dirn
    elif t@tprev<0: t=-t
    while True:
        wp=w+ds*t; W=wp.copy(); ok=False
        for it in range(15):
            f=H(W)
            if not np.all(np.isfinite(f)): break
            A=np.vstack([DH(W),t]); d=np.linalg.solve(A,np.concatenate([f,[t@(W-wp)]])); W=W-d
            if np.abs(d).max()<1e-11: ok=True; break
        if ok and np.abs(H(W)).max()<1e-8 and (W[:9]>-1).all() and np.abs((W[:9]-w[:9])/(np.abs(w[:9])+np.exp(w[9]))).max()<0.05: break
        ds*=0.5
        if ds<1e-10: break
    if ds<1e-10: print("stall"); break
    w=W; tprev=t; ds=min(ds*1.3,0.1)
    xs=np.sort(w[:9]); gap=np.min(np.diff(xs)/(np.abs(xs[:-1])+np.abs(xs[1:])))
    out.append([w[10],w[9],jinv(np.exp(w[9])),q4real(w[:9],w[9]),gap]+list(xs))
    if st%10==0: print("L=%.4f beta=%.5g j=%.4g Q4real=%d relgap=%.2e x=%s"%(w[10],np.exp(w[9]),jinv(np.exp(w[9])),out[-1][3],gap,np.array2string(xs,precision=3,max_line_width=250)),flush=True)
    if w[9]<np.log(1e-6): print("fold curve reaches the node"); break
np.save("foldcurve_%s_%+d.npy"%(sys.argv[2],int(dirn)),np.array(out))
o=np.array(out); i=np.argmax(o[:,1]); print("max beta on this run: %.5g at L=%.4f, j=%.5g; Q4 real counts seen: %s"%(np.exp(o[i,1]),o[i,0],o[i,2],sorted(set(o[:,3].astype(int)))))
