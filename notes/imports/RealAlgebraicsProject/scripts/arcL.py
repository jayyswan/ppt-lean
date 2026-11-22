# Session 36: fixed-L arc through a point of the fold curve (for L beyond the glued range). usage: python3 arcL.py foldcurve_3.0_+1.npy <L> <dir +1|-1> [steps]
import sys, numpy as np
src=open('cont.py').read()
pre=src.split("outs=[]")[0]+"def G"+src.split("def G",1)[1].split("for k,xo in enumerate(outs):")[0]
DIR=float(sys.argv[3]); maxs=int(sys.argv[4]) if len(sys.argv)>4 else 3000; o=np.load(sys.argv[1]); Lt=float(sys.argv[2]); i=np.argmin(np.abs(o[:,0]-Lt)); L=o[i,0]
sys.argv=['cont.py',str(L),'1e-3','0',str(maxs)]; exec(pre)
x=o[i,5:].copy(); s=o[i,1]; 

tang_prev=None; rows=[]; ds=0.02; steps=0; folds=0; status='maxsteps'; gap=0
if True:
    tang_prev=None; rows=[]; ds=0.02; steps=0; folds=0; status='maxsteps'
    while steps<maxsteps:
        J=GJ(x,s); Nul=np.linalg.svd(J)[2][-1]
        if tang_prev is None: Nul=Nul*DIR*np.sign(Nul[np.argmax(np.abs(Nul[:9]))])
        elif Nul@tang_prev<0: Nul=-Nul
        if tang_prev is not None and np.sign(Nul[-1])!=np.sign(tang_prev[-1]): folds+=1; print("   fold in beta at s=%.4f beta=%.4g"%(s,np.exp(s)),flush=True)
        # scale step by configuration scale
        sc=np.concatenate([np.abs(x)+1e-12+np.exp(s)*0.0,[1.0]])
        while True:
            xp=np.concatenate([x,[s]])+ds*Nul*1.0
            X=xp.copy(); ok=False
            for it in range(12):
                Gv=G(X[:9],X[9])
                if not np.all(np.isfinite(Gv)): break
                Jx=GJ(X[:9],X[9]); A=np.vstack([Jx,Nul]); bvec=np.concatenate([Gv,[Nul@(X-xp)]])
                try: d=np.linalg.solve(A,bvec)
                except np.linalg.LinAlgError: break
                X=X-d
                if np.abs(d[:9]/(np.abs(X[:9])+np.exp(X[9]))).max()<1e-12 and abs(d[9])<1e-12: ok=True; break
            relmove=np.abs((X[:9]-x)/(np.abs(x)+np.exp(s))).max() if ok else 9
            if ok and np.all(np.isfinite(X)) and relmove<0.05 and np.abs(G(X[:9],X[9])).max()<1e-9 and (X[:9]>-1).all(): break
            ds*=0.5
            if ds<1e-13: break
        if ds<1e-13: status='stall'; break
        tang_prev=Nul; x,s=X[:9],X[9]; steps+=1
        xs=np.sort(x); gap=np.min(np.diff(xs)/ (np.abs(xs[:-1])+np.abs(xs[1:])))
        if steps%10==0 or steps<3: rows.append(np.concatenate([[s,jinv(np.exp(s)),q4real(x,s),gap],xs]))
        if relmove<0.01: ds*=1.5
        ds=min(ds, 0.2)
        if s>np.log(1e4): status='reached beta=1e4'; break
        if s<np.log(1e-7): status='back to node'; break
    rows=np.array(rows); np.save(f"arc_{L:.2f}_{int(DIR):+d}.npy",rows)
    print(f"L={L} dir {DIR:+.0f}: {status} after {steps} steps, folds={folds}, final beta={np.exp(s):.4g} j={jinv(np.exp(s)):.4g}")
    # summarize Q4 real-root count transitions
    prev=None
    for r_ in rows:
        if prev is None or r_[2]!=prev: print(f"   beta={np.exp(r_[0]):.4g} j={r_[1]:.4g} Q4 real roots={int(r_[2])} relgap={r_[3]:.2e}")
        prev=r_[2]
    print("   final x:",np.array2string(np.sort(x),precision=4,max_line_width=200),"min relgap %.2e"%gap,flush=True)
    