# Session 37: branch points of U_C -> c2-line via bordered Newton (phi=0, J v=0, a.v=1),
# then the local monodromy permutation around each.
# usage: python3 branch.py <fib.pkl> <tries> <seed>
import numpy as np, sys, pickle
fib=sys.argv[1]; ntry=int(sys.argv[2]); sd=int(sys.argv[3])
sys.argv=['mono_c.py','0',str(sd)]
exec(open('mono_c.py').read().split("sols={")[0])
_,_,sols=pickle.load(open(fib,'rb')); sols=[np.array(s) for s in sols]
keys=[np.array(key(s)) for s in sols]
def ident(y):
    k=np.array(key(y))
    for i,kk in enumerate(keys):
        if np.max(np.abs(k-kk))<1e-4: return i
    return -1
def G(z,a):
    x=z[:9]; w=z[9]; v=z[10:]
    return np.concatenate([res(x,w), jac(x)@v, [a@v-1]])
def bord(x,w,it=60):
    U,s,Vh=np.linalg.svd(jac(x)); v=Vh[-1].conj(); a=v.conj()/np.vdot(v,v); 
    z=np.concatenate([x,[w],v])
    for k in range(it):
        g=G(z,a); Jz=np.zeros((19,19),complex)
        for j in range(19):
            e=np.zeros(19,complex); hh=1e-7*(1+abs(z[j])); e[j]=hh; Jz[:,j]=(G(z+e,a)-g)/hh
        try: dz=np.linalg.solve(Jz,-g)
        except: return None
        lam=1
        while lam>1e-3:
            zn=z+lam*dz
            if np.all(np.isfinite(zn)) and np.linalg.norm(G(zn,a))<np.linalg.norm(g): break
            lam/=2
        z=zn
        if np.linalg.norm(G(z,a))<1e-10: return z
    return None
bps=[]
for t in range(ntry):
    i=rng.integers(len(sols)); wt=w0+rng.uniform(0,8)*np.exp(2j*np.pi*rng.random())
    y=track(sols[i],w0,wt)
    if y is None: continue
    z=bord(y,wt)
    if z is None: continue
    x=z[:9]; sep=min(abs(x[a]-x[b]) for a in range(9) for b in range(a))
    if sep<1e-4: continue
    wb=z[9]; wb=wb.real+1j*(((wb.imag-w0.imag+np.pi)%(2*np.pi))-np.pi+w0.imag)
    if all(abs(wb-b)>1e-5 for b in bps): bps.append(wb); print('bp', np.round(wb-w0,6),'from sol',i,'sep %.2e'%sep,flush=True)
pickle.dump(bps,open('bps_%d.pkl'%sd,'wb'))
# local monodromy: go to wb + r (r small), circle, return
def local_perm(wb):
    r=0.02*max(1,abs(wb-w0)/5); base=wb+r*(w0-wb)/abs(w0-wb)
    pts=[base]+[wb+(base-wb)*np.exp(2j*np.pi*k/12) for k in range(1,13)]+[w0]
    perm=[]
    for x in sols:
        y=x; wa=w0
        for p in pts: y=track(y,wa,p) if y is not None else None; wa=p
        if y is None: perm.append(None); continue
        y,ok=newton(y,w0); perm.append(ident(y))
    return perm
for wb in bps: print('bp',np.round(wb-w0,4),'local perm',local_perm(wb),flush=True)
