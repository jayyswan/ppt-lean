# Session 37: random-start complex Newton for the fibre of U_C over a fixed c2 (fixed h).
# usage: python3 rand_fib.py <starts> <seed> [start.pkl]
import numpy as np, sys, pickle, warnings; warnings.filterwarnings('ignore')
N=int(sys.argv[1]); seed=int(sys.argv[2]); start=sys.argv[3] if len(sys.argv)>3 else 'track_end.pkl'
d,x0,c20=pickle.load(open(start,'rb')); w0=np.log(c20); rng=np.random.default_rng(seed)
def h(t): return (t-d)*(t+d)*(t+1)
def hp(t): return 3*t**2+2*t-d*d
def res(x):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,1)
    r=2*np.sum(np.log(D),axis=1)-5*np.log(h(x))-w0
    return r.real+1j*(((r.imag+np.pi)%(2*np.pi))-np.pi)
def jac(x):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,np.inf); I=1/D
    J=-2*I; np.fill_diagonal(J,2*np.sum(I,axis=1)-5*hp(x)/h(x)); return J
found={}; sv={}
roots=np.array([d,-d,-1])
for s in range(N):
    sc=10**rng.uniform(-1,1.5)
    x=sc*(rng.normal(size=9)+1j*rng.normal(size=9))
    if rng.random()<0.5: x[0]=10**rng.uniform(1,3)*np.exp(2j*np.pi*rng.random())
    ok=False
    for it in range(200):
        try: dx=np.linalg.solve(jac(x),-res(x))
        except: break
        lam=1.0
        r0=np.linalg.norm(res(x))
        while lam>1e-4:
            xn=x+lam*dx
            if np.all(np.isfinite(xn)) and np.linalg.norm(res(xn))<r0: break
            lam/=2
        x=xn
        if not np.all(np.isfinite(x)): break
        if np.linalg.norm(res(x))<1e-11: ok=True; break
    if not ok: continue
    sep=min(abs(x[i]-x[j]) for i in range(9) for j in range(i))
    dh=np.min(np.abs(x[:,None]-roots[None,:]))
    if sep<1e-4 or dh<1e-4 or np.max(np.abs(x))>1e8: continue
    k=tuple(np.round(np.sort_complex(x),5))
    found[k]=found.get(k,0)+1
    if k not in sv: sv[k]=x
print('starts',N,'distinct genuine solutions',len(found))
for k,v in sorted(found.items(),key=lambda kv:-kv[1]): print(v, np.round(np.array(k)[:4],4))
pickle.dump((d,w0,list(sv.values())),open('fib_rand_%d.pkl'%seed,'wb'))
