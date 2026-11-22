# Session 37: monodromy permutations of the 5-point fibre of U_C -> c2-line (exec's tracker from mono_c.py).
# usage: python3 perm.py <fib.pkl> <loops> <seed>
import numpy as np, sys, pickle
fib=sys.argv[1]; nl=int(sys.argv[2]); sd=int(sys.argv[3])
sys.argv=['mono_c.py','0',str(sd)]
exec(open('mono_c.py').read().split("sols={")[0])
_,_,S=pickle.load(open(fib,'rb'))
S=[np.array(s) for s in S]+[x0]
keys=[]; sols=[]
for s in S:
    k=key(s)
    if all(np.max(np.abs(np.array(k)-np.array(kk)))>1e-4 for kk in keys): keys.append(k); sols.append(s)
n=len(sols); print('fibre size',n)
def ident(y):
    k=np.array(key(y)); dist=[np.max(np.abs(k-np.array(kk))) for kk in keys]; i=int(np.argmin(dist))
    return i if dist[i]<1e-4 else -1
def loop(pts):
    perm=[]
    for x in sols:
        y=x; wa=w0
        for wb in pts:
            y=track(y,wa,wb) if y is not None else None; wa=wb
        if y is None: perm.append(None); continue
        y,ok=newton(y,w0); perm.append(ident(y))
    return perm
def loop_pts():
    r=rng.uniform(0.3,8); a=w0+r*np.exp(2j*np.pi*rng.random()); b=a+rng.uniform(0.3,6)*np.exp(2j*np.pi*rng.random())
    return [a,b,w0]
print('wind c2 around 0:',loop([w0+2j*np.pi*k/6 for k in range(1,7)]))
for L in range(nl):
    pts=loop_pts(); print([np.round(p-w0,2) for p in pts], loop(pts),flush=True)
