# Find lines on D = {Q4=Q5=0} in trace-zero C^9 via moment form; save configs (a_i,b_i).
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def vec(u): return np.concatenate([[-u.sum()], u])
def P(z,k): return np.sum(z**k)
def Q4(z): return 6*P(z,4)-P(z,2)**2
def Q5(z): return 18*P(z,5)-5*P(z,2)*P(z,3)
def coeffs(f,deg,a,b):
    ts=np.exp(2j*np.pi*np.arange(deg+1)/(deg+1)); v=np.array([f(a+t*b) for t in ts]); return np.fft.fft(v)/(deg+1)
def eqs(x):
    a,b=vec(x[:8]),vec(x[8:]); return np.concatenate([coeffs(Q4,4,a,b),coeffs(Q5,5,a,b)])
def jac(F,y,h=1e-7):
    f0=F(y); J=np.zeros((len(f0),len(y)),complex)
    for j in range(len(y)):
        e=np.zeros(len(y),complex); e[j]=h; J[:,j]=(F(y+e)-f0)/h
    return J
def full(y): return np.concatenate([[1,0],y[:6],[0,1],y[6:]])
def solve(ns):
    L=rng.normal(size=(ns,12))+1j*rng.normal(size=(ns,12)); c=rng.normal(size=ns)+1j*rng.normal(size=ns)
    F=lambda y: np.concatenate([eqs(full(y)),L@y-c])
    y=rng.normal(size=12)+1j*rng.normal(size=12)
    for it in range(100):
        f=F(y)
        if np.linalg.norm(f)<1e-12: break
        y=y+np.linalg.lstsq(jac(F,y),-f,rcond=None)[0]
        if np.linalg.norm(y)>1e6: return None
    return full(y) if np.linalg.norm(F(y))<1e-10 else None
out=[]
for t in range(int(sys.argv[2]) if len(sys.argv)>2 else 40):
    x=solve(2)
    if x is None: continue
    a,b=vec(x[:8]),vec(x[8:])
    if min(abs(a[i]-a[j])+abs(b[i]-b[j]) for i in range(9) for j in range(i+1,9))<1e-6: continue
    out.append(np.concatenate([a,b]))
np.save('dl_%s.npy'%(sys.argv[1] if len(sys.argv)>1 else 1),np.array(out)); print(len(out))
