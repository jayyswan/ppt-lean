import numpy as np, sys, pickle
seed=int(sys.argv[1]); nloops=int(sys.argv[2]); rad=float(sys.argv[3])
sys.argv=['x',str(seed)]
exec(open('defl.py').read().split('X=np.concatenate')[0])
def H(Y,c):
    y=Y[:12]; x=full(y); a,b=vec(x[:8]),vec(x[8:]); return np.concatenate([G(Y),invs(a,b)-c])
def correct(Y,c,it=12):
    for k in range(it):
        f=H(Y,c)
        if np.linalg.norm(f)<1e-12: break
        Y=Y+np.linalg.lstsq(jac(lambda v:H(v,c),Y),-f,rcond=None)[0]
    return Y,np.linalg.norm(H(Y,c))
def ab(Y): x=full(Y[:12]); return vec(x[:8]),vec(x[8:])
def gram(Y):
    a,b=ab(Y); P,Q,T=moments(a,b); return P@np.linalg.inv(Q)@P.T
X=np.load('dl_%d.npy'%(1+seed%4)); row=X[seed%len(X)]
a,b=row[:9],row[9:]; g=np.linalg.inv(np.array([[a[1],b[1]],[a[2],b[2]]]).T); A2=g@np.stack([a,b]); a2,b2=A2
M=M9(a2,b2); N=np.linalg.svd(M)[2][-2:].T.conj(); V=N@np.linalg.solve(R@N,np.eye(2))
Y0=np.concatenate([a2[3:9],b2[3:9],V[:,0],V[:,1]]); Y0,_=correct(Y0,invs(a2,b2))
c0=invs(*ab(Y0)); G0=gram(Y0); found=[]
rng2=np.random.default_rng(seed+100)
def track(Y,path,steps=30):
    for p,q in zip(path[:-1],path[1:]):
        for s in np.linspace(0,1,steps+1)[1:]:
            Y,r=correct(Y,p+(q-p)*s)
            if r>1e-9: return None
    return Y
for loop in range(nloops):
    d1=(rng2.normal(size=2)+1j*rng2.normal(size=2))*abs(c0)*rad; d2=(rng2.normal(size=2)+1j*rng2.normal(size=2))*abs(c0)*rad
    Y=track(Y0,[c0,c0+d1,c0+d2,c0])
    if Y is None: print(loop,'fail',flush=True); continue
    sig=match(G0,gram(Y))
    print(loop,'perm' if sig else 'other', sig if sig else np.round(np.sort(np.abs(np.diag(gram(Y))))[:3],4),flush=True)
    if sig: found.append(sig)
pickle.dump(found,open('perms_%d.pkl'%seed,'wb'))
print('G0 diag',np.round(np.sort(np.abs(np.diag(G0)))[:3],4))
