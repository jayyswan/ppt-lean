# Session 36: continue real S_ord lines on the one-component side from the nodal end (beta small) to beta large
# h = (x+1)(x^2+beta^2), equal-potential system V_i = sum_{j!=i} log|x_i-x_j| - 2.5 log h(x_i) = L (L fixed),
# pseudo-arclength in (x, s = log beta). Tracks j, Q4|line real roots, min |x_i - x_j|, folds in beta.
# usage (stops at first fold): python3 fold.py <L> <beta0> [seed] [maxsteps]     writes cont_<L>_<k>.npy  (rows: s, j, nQ4real, x_1..x_9)
import sys, numpy as np
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
L=float(sys.argv[1]); beta0=float(sys.argv[2]); seed=int(sys.argv[3]) if len(sys.argv)>3 else 0
maxsteps=int(sys.argv[4]) if len(sys.argv)>4 else 4000
rng=np.random.default_rng(seed)

def newton_real(x,F,J,iters=60):
    for _ in range(iters):
        r=F(x); dx=np.linalg.lstsq(J(x),r,rcond=None)[0]
        sc=min(1,0.2*np.min(np.abs(x)+1e-3)/max(np.abs(dx).max(),1e-300)); x=x-sc*dx
    return x,np.abs(F(x)).max()
def Wout(x):
    d=x[:,None]-x[None,:]; np.fill_diagonal(d,1)
    return np.log(np.abs(d)).sum(1)+np.log(np.abs(x))-2.5*np.log(x+1)-L
def Jout(x):
    d=x[:,None]-x[None,:]; np.fill_diagonal(d,1); iD=1/d; np.fill_diagonal(iD,0)
    J=-iD; np.fill_diagonal(J,iD.sum(1)+1/x-2.5/(x+1)); return J
outs=[]
for _ in range(3000):
    x0=-1+np.exp(rng.uniform(-4,8,3))
    with np.errstate(all='ignore'):
        try: x,r=newton_real(x0,Wout,Jout)
        except Exception: continue
    if np.isfinite(r) and r<1e-11 and (x>-1).all() and np.min(np.abs(x))>1e-6:
        xs=np.sort(x)
        if np.min(np.diff(xs))>1e-8 and not any(np.allclose(xs,q) for q in outs): outs.append(xs)

def G(x,s):   # residual
    b2=np.exp(2*s); d=x[:,None]-x[None,:]; np.fill_diagonal(d,1)
    return np.log(np.abs(d)).sum(1)-2.5*np.log((x+1)*(x*x+b2))-L
def GJ(x,s):  # 9x10 jacobian wrt (x, s)
    b2=np.exp(2*s); d=x[:,None]-x[None,:]; np.fill_diagonal(d,1); iD=1/d; np.fill_diagonal(iD,0)
    J=-iD; np.fill_diagonal(J,iD.sum(1)-2.5*(1/(x+1)+2*x/(x*x+b2)))
    js=-2.5*2*b2/(x*x+b2)
    return np.hstack([J,js[:,None]])
def jinv(beta):
    e1,e2,e3=-1,1j*beta,-1j*beta; lam=(e3-e1)/(e2-e1)
    return (256*(lam*lam-lam+1)**3/(lam*lam*(lam-1)**2)).real
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

for k,xo in enumerate(outs):
    K=np.exp(2*(L-np.sum(np.log(np.abs(xo)))))
    if not (0<K<3.45): print("outer",np.round(xo,4),"K=%.3g no real core"%K); continue
    cs=all_solutions(6,K,600,rng,rounds=2); t=np.sort(cs[0].real)
    s=np.log(beta0); x=np.concatenate([beta0*t,xo])
    x,r=newton_real(x,lambda v:G(v,s),lambda v:GJ(v,s)[:,:9],80)
    if r>1e-10: print("glue failed",r); continue
    # pseudo-arclength in scaled coords: u = (asinh-ish) use w = x directly but step control by relative change
    tang_prev=None; rows=[]; ds=0.02; steps=0; folds=0; status='maxsteps'
    while steps<maxsteps:
        J=GJ(x,s); Nul=np.linalg.svd(J)[2][-1]
        if tang_prev is None: Nul=Nul*np.sign(Nul[-1])
        elif Nul@tang_prev<0: Nul=-Nul
        if tang_prev is not None and np.sign(Nul[-1])!=np.sign(tang_prev[-1]): folds+=1; status='fold'; break
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
        if steps%5==0 or steps<3: rows.append(np.concatenate([[s,jinv(np.exp(s)),q4real(x,s),gap],xs]))
        if relmove<0.01: ds*=1.5
        ds=min(ds, 0.2)
        if s>np.log(1e4): status='reached beta=1e4'; break
        if s<np.log(1e-7): status='back to node'; break
    rows=np.array(rows); np.save(f"fold_{L}_{k}.npy",rows)
    print(f"L={L} outer#{k} K={K:.3f}: {status} after {steps} steps, folds={folds}, final beta={np.exp(s):.4g} j={jinv(np.exp(s)):.4g}")
    # summarize Q4 real-root count transitions
    prev=None
    for r_ in rows:
        if prev is None or r_[2]!=prev: print(f"   beta={np.exp(r_[0]):.4g} j={r_[1]:.4g} Q4 real roots={int(r_[2])} relgap={r_[3]:.2e}")
        prev=r_[2]
    print("   final x:",np.array2string(np.sort(x),precision=4,max_line_width=200),"min relgap %.2e"%gap,flush=True)
