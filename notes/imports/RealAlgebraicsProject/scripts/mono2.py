# Session 37: monodromy solver for the fibre of U_C -> c2-line, seeded by known solutions.
# usage: python3 mono2.py <in.pkl> <loops> <seed> <out.pkl>   (in.pkl: (d,w0,list of x))
import numpy as np, sys, pickle
inp=sys.argv[1]; nl=int(sys.argv[2]); sd=int(sys.argv[3]); out=sys.argv[4]
sys.argv=['mono_c.py','0',str(sd)]
exec(open('mono_c.py').read().split("sols={")[0])
_,_,S=pickle.load(open(inp,'rb'))
S=[np.array(s) for s in S]+[x0]
keys=[]; sols=[]
def ident(y):
    k=np.array(key(y))
    for i,kk in enumerate(keys):
        if np.max(np.abs(k-np.array(kk)))<1e-4: return i
    return -1
def add(y):
    if ident(y)<0: keys.append(key(y)); sols.append(y); return True
    return False
for s in S: add(s)
print('start',len(sols),flush=True)
def lp():
    r=rng.uniform(0.3,9); a=w0+r*np.exp(2j*np.pi*rng.random()); b=a+rng.uniform(0.3,6)*np.exp(2j*np.pi*rng.random())
    return [a,b,w0]
for L in range(nl):
    pts=lp(); perm=[]
    for x in list(sols):
        y=x; wa=w0
        for wb in pts: y=track(y,wa,wb) if y is not None else None; wa=wb
        if y is None: perm.append(None); continue
        y,ok=newton(y,w0)
        sep=min(abs(y[a]-y[b]) for a in range(9) for b in range(a))
        if not ok or sep<1e-5: perm.append('deg'); continue
        new=add(y); perm.append(ident(y))
    print('loop',L,'n',len(sols),perm,flush=True)
    pickle.dump((d,w0,sols),open(out,'wb'))
