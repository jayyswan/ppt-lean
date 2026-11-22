import numpy as np, sys, pickle
part=int(sys.argv[1]); nparts=int(sys.argv[2])
sys.argv=['x','1']
exec(open('mono9b.py').read().split('X=np.load')[0].replace("seed=int(sys.argv[1]); nloops=int(sys.argv[2]); rad=float(sys.argv[3])","seed=1"))
X=np.concatenate([np.load('dl_%d.npy'%s) for s in [1,2,3,4]])
def track(Y,path,steps=30):
    for p,q in zip(path[:-1],path[1:]):
        for s_ in np.linspace(0,1,steps+1)[1:]:
            Y,r=correct(Y,p+(q-p)*s_)
            if r>1e-9: return None
    return Y
cstar=np.array([0.31+0.05j,0.24-0.02j])
res=[]
for idx in range(part,len(X),nparts):
    row=X[idx]; a,b=row[:9],row[9:]
    try:
        g=np.linalg.inv(np.array([[a[1],b[1]],[a[2],b[2]]]).T); a2,b2=g@np.stack([a,b])
        N=np.linalg.svd(M9(a2,b2))[2][-2:].T.conj(); V=N@np.linalg.solve(R@N,np.eye(2))
        Y0=np.concatenate([a2[3:9],b2[3:9],V[:,0],V[:,1]]); c0=invs(a2,b2); Y0,r=correct(Y0,c0)
        mid=(c0+cstar)/2+ (np.random.default_rng(idx).normal(size=2)+1j*np.random.default_rng(idx+7).normal(size=2))*0.3*abs(c0-cstar)
        Y=track(Y0,[c0,mid,cstar],steps=40)
    except Exception as e: print(repr(e)); Y=None
    if Y is None: print(idx,'fail',flush=True); continue
    Gm=gram(Y); res.append(Gm); print(idx,'ok',np.round(np.sort_complex(np.diag(Gm))[:3],5),flush=True)
pickle.dump(res,open('fib_%d.pkl'%part,'wb'))
