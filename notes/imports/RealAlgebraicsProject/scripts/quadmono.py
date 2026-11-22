"""Session 55: monodromy of the 4th vertices Q' (fibre of Sigma -> l1) as x1 = Q + a v1 loops.
Usage: quadmono.py <seed> <loops>   (reads quad55_<seed>.npy written by quad55.py; same seed)"""
import sys, numpy as np
exec(open('quad55.py').read().split("\ndef main")[0])
seed,loops=int(sys.argv[1]),int(sys.argv[2])
rng,Q,v1,v3,x1=setup(seed)
l0,l1=rnd(rng,n),rnd(rng,n)   # same draws as quad55 main
d=np.load(f'quad55_{seed}.npy')
a0=(x1-Q)@v1.conj()/(v1@v1.conj())
def zfrom(row,a):
    Qp,x3=row[:9],row[9:18]; t,s=row[-2],row[-1]
    v=(Qp-(Q+a*v1))/t
    return np.concatenate([v,[t,s]])
Z0=[zfrom(r,a0) for r in d]
def solve_at(z,a):
    F,J=system(Q,v1,v3,Q+a*v1,l0,l1)
    for _ in range(30):
        f=F(z)
        if np.linalg.norm(f)<1e-12: return z
        z=z+np.linalg.lstsq(J(z),-f,rcond=None)[0]
    return z if np.linalg.norm(F(z))<1e-9 else None
def track(z,path):
    for a in path[1:]:
        z=solve_at(z,a)
        if z is None: return None
    return z
def key(z,a): 
    Qp=Q+a*v1+z[n]*z[:n]; return canon(Qp)
K0=[key(z,a0) for z in Z0]
rs=np.random.default_rng(seed+100+int(sys.argv[5]) if len(sys.argv)>5 else seed+100)
perms=[]
for L in range(loops):
    c=a0+(rs.standard_normal()+1j*rs.standard_normal())*float(sys.argv[4]) if len(sys.argv)>4 else (rs.standard_normal()+1j*rs.standard_normal())*0.6
    R=abs(c-a0)
    th=np.linspace(0,2*np.pi,int(sys.argv[3]) if len(sys.argv)>3 else 1200)
    path=c+(a0-c)*np.exp(1j*th)
    p=[]
    for z in Z0:
        zz=track(z.copy(),path)
        if zz is None: p.append(-1); continue
        k=key(zz,a0); dist=[np.linalg.norm(k-k0) for k0 in K0]
        j=int(np.argmin(dist)); p.append(j if dist[j]<1e-6 else -1)
    ok = -1 not in p and len(set(p))==len(p)
    print('loop',L,'ok' if ok else 'BAD', 'moved',sum(1 for i,j in enumerate(p) if i!=j), flush=True)
    if ok: perms.append(p)
# orbits
par=list(range(len(Z0)))
def f(i):
    while par[i]!=i: i=par[i]
    return i
for p in perms:
    for i,j in enumerate(p): par[f(i)]=f(j)
orb={}
for i in range(len(Z0)): orb.setdefault(f(i),[]).append(i)
print('good loops',len(perms),'orbit sizes',sorted(len(o) for o in orb.values()))
import pickle
pickle.dump(perms, open(f'quadmono_{seed}_{sys.argv[5] if len(sys.argv)>5 else 0}.pkl','wb'))
print('fixed by all good loops:', [i for i in range(len(Z0)) if all(p[i]==i for p in perms)])
