"""Session 31: structure of C_b^pen. For each pencil conic: pencil of cubics through
the 9 points [q_i] in P^2 (coords (c0,c1,c2) of Q(t)=c0+c1 t+c2 t^2, discriminant
c1^2-4c0c2), the harmonic member H, singularities of H, the sextic H|Delta."""
import numpy as np, itertools
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
P=[Q for Q,l in zip(Qs,lab) if l=='pencil']
mon=[e for e in itertools.product(range(4),repeat=3) if sum(e)==3]
def ev(coef,x): return sum(c*np.prod(x**np.array(e)) for c,e in zip(coef,mon))
def lap(coef):
    # Laplacian dual to Delta = c1^2-4c0c2:  d1^2 - d0 d2 (up to scale)
    out=np.zeros(3)  # coefficients of resulting linear form in c0,c1,c2
    for c,e in zip(coef,mon):
        e=list(e)
        if e[1]>=2:
            f=e.copy(); f[1]-=2; out[f.index(1)]+=c*e[1]*(e[1]-1)
        if e[0]>=1 and e[2]>=1:
            f=e.copy(); f[0]-=1; f[2]-=1; out[f.index(1)]-=c*e[0]*e[2]
    return out
for Q in P:
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([[np.prod(x**np.array(e)) for e in mon] for x in q])
    _,s,vt=np.linalg.svd(M); B=vt[-2:]
    L=np.array([lap(b) for b in B]).T   # 3x2
    _,sl,vl=np.linalg.svd(L); ab=vl[-1]
    H=ab@B
    # sextic: H(1,-2u,u^2)
    from numpy.polynomial import polynomial as Pl
    sx=np.zeros(7)
    for c,e in zip(H,mon):
        term=Pl.polymul(Pl.polypow([0,-2],e[1]),Pl.polypow([0,0,1],e[2]))
        sx[:len(term)]+=c*term
    r=np.roots(sx[::-1])
    # singular points of H: grad=0, solve numerically via random restarts
    def grad(x):
        g=np.zeros(3,complex)
        for c,e in zip(H,mon):
            for k in range(3):
                if e[k]:
                    f=list(e); f[k]-=1; g[k]+=c*e[k]*np.prod(x**np.array(f))
        return g
    # discriminant check: min over sphere of |grad| via many random complex starts + Newton
    best=1e9
    rng=np.random.default_rng(0)
    for st in range(60):
        x=rng.normal(size=3)+1j*rng.normal(size=3); x/=np.linalg.norm(x)
        for it in range(60):
            h=1e-7; g=grad(x)
            Jg=np.array([(grad(x+h*np.eye(3)[k])-g)/h for k in range(3)]).T
            A=np.vstack([Jg,x.conj()[None]]); bb=np.append(g,0)
            dx=np.linalg.lstsq(A,bb,rcond=None)[0]; x=x-dx; x/=np.linalg.norm(x)
        best=min(best,np.linalg.norm(grad(x)))
    print('lap-sv',np.round(sl,12),' sextic roots',np.round(np.sort_complex(r),4),' min|grad|',f'{best:.1e}')
