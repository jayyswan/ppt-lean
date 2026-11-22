# Session 51: smooth real points of V_k = {p1..pk = 0} in R^r x C^s; charpoly shape, real-root count,
# Jacobian rank (smoothness) and coordinate separation (K = P(y) open condition).
import sys, numpy as np
n,k,r,seed,N=[int(a) for a in sys.argv[1:6]]; s=(n-r)//2; rng=np.random.default_rng(seed)
def zc(u):
    w=u[r::2]+1j*u[r+1::2]; return np.concatenate([u[:r].astype(complex),w,np.conj(w)])
def F(u):
    z=zc(u); return np.array([np.sum(z**j).real for j in range(1,k+1)]+[u@u-1])
def J(u): return np.array([(F(u+h)-F(u-h))/2e-7 for h in np.eye(n)*1e-7]).T
good=0; out=[]
for t in range(N):
    u=rng.normal(size=n)
    for it in range(80):
        f=F(u); u=u+np.linalg.lstsq(J(u),-f,rcond=None)[0]
        if not np.isfinite(u).all() or np.linalg.norm(f)<1e-14: break
    if not np.isfinite(u).all() or np.linalg.norm(F(u))>1e-11: continue
    z=zc(u); c=np.poly(z).real
    rank=np.linalg.matrix_rank(J(u)[:k],1e-8); sep=min(abs(z[i]-z[j]) for i in range(n) for j in range(i))
    nr=int(sum(abs(np.roots(c).imag)<1e-7))
    out.append((rank,round(sep,3),nr,[n-i for i,x in enumerate(c) if abs(x)>1e-9][1:3]))
    good+=1
print(f'n={n} k={k} r={r}: {good}/{N} converged'); 
for o in out[:5]: print('  jac rank, min sep, real roots, top degrees after x^n:',o)
