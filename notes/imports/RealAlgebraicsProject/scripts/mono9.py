import numpy as np, sys, itertools
exec(open('lines.py').read().split('out=[]')[0].replace("rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)","rng=np.random.default_rng(int(sys.argv[1]))"))
def moments(a,b):
    P=np.stack([a,b],1); Q=P.T@P
    T=np.einsum('ni,nj,nk->ijk',P,P,P); return P,Q,T
def invs(a,b):
    P,Q,T=moments(a,b); Qi=np.linalg.inv(Q)
    J2=np.einsum('ijk,lmn,il,jm,kn->',T,T,Qi,Qi,Qi)
    A,B_,C,D=T[0,0,0],3*T[0,0,1],3*T[0,1,1],T[1,1,1]
    disc=B_**2*C**2-4*A*C**3-4*B_**3*D-27*A**2*D**2+18*A*B_*C*D
    return np.array([disc/np.linalg.det(Q)**3, J2])
def F(y,c):
    x=full(y); a,b=vec(x[:8]),vec(x[8:]); return np.concatenate([eqs(x),invs(a,b)-c])
def correct(y,c,it=150):
    for k in range(it):
        f=F(y,c)
        if np.linalg.norm(f)<1e-12: break
        y=y+np.linalg.lstsq(jac(lambda v:F(v,c),y),-f,rcond=None)[0]
    return y,np.linalg.norm(F(y,c))
def gram(y):
    x=full(y); a,b=vec(x[:8]),vec(x[8:]); P,Q,T=moments(a,b); return P@np.linalg.inv(Q)@P.T
def match(G0,G1):
    n0,n1=np.diag(G0),np.diag(G1); sig=[]
    for i in range(9):
        j=np.argmin(abs(n1-n0[i]))
        if abs(n1[j]-n0[i])>1e-6*(1+abs(n0[i])): return None
        sig.append(j)
    if len(set(sig))<9: return None
    if np.abs(G1[np.ix_(sig,sig)]-G0).max()>1e-6: return None
    return tuple(sig)
# start: a line from solve
while True:
    x=solve(2)
    if x is not None: break
y0=np.concatenate([x[2:8],x[10:16]]); a,b=vec(x[:8]),vec(x[8:]); c0=invs(a,b)
G0=gram(y0); perms=set()
rng2=np.random.default_rng(int(sys.argv[1])+100)
for loop in range(int(sys.argv[2])):
    # loop: c0 -> c0+d1 -> c0+d2 -> c0 (triangle) in C^2
    d1=(rng2.normal(size=2)+1j*rng2.normal(size=2))*abs(c0)*float(sys.argv[3]); d2=(rng2.normal(size=2)+1j*rng2.normal(size=2))*abs(c0)*float(sys.argv[3])
    path=[c0,c0+d1,c0+d2,c0]; y=y0.copy(); ok=True
    for p,q in zip(path[:-1],path[1:]):
        for s in np.linspace(0,1,41)[1:]:
            y,r=correct(y,p+(q-p)*s)
            if r>1e-7: ok=False; print('r',r,s); break
        if not ok: break
    if not ok: print('fail'); continue
    sig=match(G0,gram(y))
    print(loop,'perm' if sig else 'other config', sig if sig and sig!=tuple(range(9)) else '')
    if sig: perms.add(sig)
import pickle; pickle.dump(perms,open('perms_%s.pkl'%sys.argv[1],'wb'))
