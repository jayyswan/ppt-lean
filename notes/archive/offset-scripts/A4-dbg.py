import numpy as np, mpmath as mp
mp.mp.dps=60
src=open(r'C:\dev\Powerpoint\lean\archived files\offset-scripts\A4-03-chain-degree.py').read().split('def fit_degree')[0]
exec(src)

def spectrum(n, Nmax=16, npts=300):
    # cheap mpmath sample then cast down
    ts=[mp.mpf(2*k-1)/npts for k in range(1,npts+1)]
    pts=[]
    for t in ts:
        pts.append(chain(n,t))
    Xs=np.array([float(p[0]) for p in pts]); Ys=np.array([float(p[1]) for p in pts])
    Xs=(Xs-Xs.mean())/Xs.std(); Ys=(Ys-Ys.mean())/Ys.std()
    out=[]
    for N in range(1,Nmax+1):
        mons=[(i,j) for i in range(N+1) for j in range(N+1-i)]
        if len(mons)>=npts:
            out.append((N,len(mons),None)); continue
        A=np.array([[X**i*Y**j for (i,j) in mons] for X,Y in zip(Xs,Ys)])
        # scale each column to unit norm for conditioning
        A=A/np.linalg.norm(A,axis=0,keepdims=True)
        S=np.linalg.svd(A,compute_uv=False)
        out.append((N,len(mons),S[-1]))
    return out

for n in (1,2,3):
    print("n=",n)
    prev=None
    for (N,m,s) in spectrum(n):
        if s is None:
            print("  N=%2d m=%3d  (underdetermined)"%(N,m)); continue
        jump = "" if prev is None else "  ratio_prev=%.1e"%(prev/max(s,1e-300))
        print("  N=%2d m=%3d  sigma_min=%.3e%s"%(N,m,s,jump))
        prev=s
