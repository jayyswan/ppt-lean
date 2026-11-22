"""Session 31: singular points of the harmonic cubic H of C_b^pen (and control:
the unique cubic through the 9 points of generic C_b conics)."""
import numpy as np, itertools
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
mon=[e for e in itertools.product(range(4),repeat=3) if sum(e)==3]
exec(open('pen_an.py').read().split('for Q in P:')[0].split("Qs=np.load")[0])
def lap(coef):
    out=np.zeros(3)
    for c,e in zip(coef,mon):
        e=list(e)
        if e[1]>=2:
            f=e.copy(); f[1]-=2; out[f.index(1)]+=c*e[1]*(e[1]-1)
        if e[0]>=1 and e[2]>=1:
            f=e.copy(); f[0]-=1; f[2]-=1; out[f.index(1)]-=c*e[0]*e[2]
    return out
def cubic_of(Q,harm=True):
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([[np.prod(x**np.array(e)) for e in mon] for x in q])
    _,s,vt=np.linalg.svd(M)
    if not harm: return vt[-1]
    B=vt[-2:]; L=np.array([lap(b) for b in B]).T
    return np.linalg.svd(L)[2][-1]@B
def grad(H,x):
    g=np.zeros(3,complex)
    for c,e in zip(H,mon):
        for k in range(3):
            if e[k]:
                f=list(e); f[k]-=1; g[k]+=c*e[k]*np.prod(x**np.array(f))
    return g
def hess(H,x,h=1e-6):
    return np.array([(grad(H,x+h*np.eye(3)[k])-grad(H,x-h*np.eye(3)[k]))/(2*h) for k in range(3)])
def sings(H,starts=80):
    rng=np.random.default_rng(1); pts=[]
    for st in range(starts):
        x=rng.normal(size=3)+1j*rng.normal(size=3); x/=np.linalg.norm(x)
        for it in range(50):
            g=grad(H,x); Jg=hess(H,x)
            A=np.vstack([Jg,x.conj()[None]]); dx=np.linalg.lstsq(A,np.append(g,0),rcond=None)[0]
            x=x-dx; x/=np.linalg.norm(x)
        if np.linalg.norm(grad(H,x))<1e-10:
            x=x/x[np.argmax(abs(x))]
            if not any(np.linalg.norm(x-p)<1e-6 for p in pts): pts.append(x)
    return pts
Delta=lambda x: x[1]**2-4*x[0]*x[2]
for Q,l in zip(Qs,lab):
    if l!='pencil': continue
    H=cubic_of(Q); S=sings(H)
    info=[]
    for p in S:
        hs=hess(H,p); ev=np.linalg.svd(hs,compute_uv=False)
        info.append((np.round(p,4), 'hess-sv',np.round(ev/ev[0],6), 'Delta',np.round(Delta(p),4), 'real',np.allclose(p.imag,0,atol=1e-8)))
    print(len(S), info)
print('--- control: cubic through generic C_b points')
k=0
for Q,l in zip(Qs,lab):
    if l!='gen': continue
    H=cubic_of(Q,False); print(len(sings(H,30)), end=' '); k+=1
    if k>15: break
print()
