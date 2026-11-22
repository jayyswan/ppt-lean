# Session 37: monodromy count of the fibre of U_C -> (c^2-line), U_C = S_ord fibre over a fixed curve
# C: y^2 = h(x), h = (x-d)(x+d)(x+1), modulo S_9 (so a point of U_C is a polynomial F).
# Fibre over c2: all F (deg 9, squarefree) with F'(x_i)^2 = c2 h(x_i)^5 at every root.
# Unknowns x_1..x_9, path parameter w = log c2.  phi_i = 2 sum_j log(x_i-x_j) - 5 log h(x_i) - w.
# usage: python3 mono_c.py <loops> <seed> [start.pkl=track_end.pkl] [out=fib.pkl]
import numpy as np, sys, pickle, warnings; warnings.filterwarnings('ignore')
loops=int(sys.argv[1]); seed=int(sys.argv[2])
start=sys.argv[3] if len(sys.argv)>3 else 'track_end.pkl'
out=sys.argv[4] if len(sys.argv)>4 else 'fib.pkl'
d,x0,c20=pickle.load(open(start,'rb')); x0=np.array(x0,complex); w0=np.log(c20)
rng=np.random.default_rng(seed)
def h(t): return (t-d)*(t+d)*(t+1)
def hp(t): return 3*t**2+2*t-d*d
def res(x,w):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,1)
    r=2*np.sum(np.log(D),axis=1)-5*np.log(h(x))-w
    return (r.imag+np.pi)%(2*np.pi)-np.pi*1j*0 if False else r.real+1j*(((r.imag+np.pi)%(2*np.pi))-np.pi)
def jac(x):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,np.inf); I=1/D
    J=-2*I; np.fill_diagonal(J,2*np.sum(I,axis=1)-5*hp(x)/h(x)); return J
def newton(x,w,it=8,tol=1e-12):
    for k in range(it):
        r=res(x,w); dx=np.linalg.solve(jac(x),-r); x=x+dx
        if np.max(np.abs(dx)/(1+np.abs(x)))<tol: return x,True
    return x,np.max(np.abs(res(x,w)))<1e-9
def track(x,wa,wb):
    t=0.0; dt=0.02
    while t<1:
        dt=min(dt,1-t); w1=wa+(wb-wa)*(t+dt)
        # Euler-type predictor along tangent dx/dw = J^{-1} 1
        tg=np.linalg.solve(jac(x),np.ones(9,complex))
        xp=x+tg*(wb-wa)*dt
        xn,ok=newton(xp,w1)
        mv=np.max(np.abs(xn-xp)/(np.abs(xn)+0.05))
        if ok and np.all(np.isfinite(xn)) and mv<0.05:
            x=xn; t+=dt; dt=min(dt*1.6,0.1)
        else:
            dt/=2
            if dt<1e-7: return None
    return x
def key(x):
    s=np.sort_complex(np.round(x,6)); return tuple(s)
sols={key(x0):x0}
def loop_pts():
    if rng.random()<0.15:
        return [w0+2j*np.pi*k/4 for k in range(1,4)]+[w0+2j*np.pi]   # winding loop around c2=0
    r=rng.uniform(0.3,4); a=w0+r*np.exp(2j*np.pi*rng.random()); b=a+rng.uniform(0.3,3)*np.exp(2j*np.pi*rng.random())
    return [a,b,w0]
hist=[]
for L in range(loops):
    pts=loop_pts(); new=0
    for kx,x in list(sols.items()):
        y=x; wa=w0
        for wb in pts:
            y=track(y,wa,wb) if y is not None else None; wa=wb
        if y is None: continue
        y,ok=newton(y,w0)
        sep=min(abs(y[i]-y[j]) for i in range(9) for j in range(i))
        if ok and sep>1e-4 and key(y) not in sols: sols[key(y)]=y; new+=1
    hist.append(len(sols)); print('loop',L,'sols',len(sols),'new',new,flush=True)
    pickle.dump((d,w0,list(sols.values())),open(out,'wb'))
