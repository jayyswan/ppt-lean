# Session 37: move all fibre sheets of U_C to a rational curve h = (x-d)(x+d)(x+1), d^2 = D2 (rational),
# and rational c2; polish at 60 digits; print the resolvent prod (T - e1(F_k)) and e2 version.
# usage: python3 resolv.py <fib.pkl> <D2> <c2> [steps]
import numpy as np, sys, pickle, warnings; warnings.filterwarnings('ignore')
import mpmath as mp
fib=sys.argv[1]; D2=float(sys.argv[2]); C2=float(sys.argv[3]); steps=int(sys.argv[4]) if len(sys.argv)>4 else 400
d0,w0,sols=pickle.load(open(fib,'rb')); sols=[np.array(s,complex) for s in sols]
dend=np.sqrt(complex(D2)); 
if abs(dend-d0)>abs(-dend-d0): dend=-dend
wend=np.log(C2)
def res(x,d,w):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,1)
    h=(x-d)*(x+d)*(x+1)
    r=2*np.sum(np.log(D),axis=1)-5*np.log(h)-w
    return r.real+1j*(((r.imag+np.pi)%(2*np.pi))-np.pi)
def jac(x,d):
    D=x[:,None]-x[None,:]; np.fill_diagonal(D,np.inf); I=1/D
    h=(x-d)*(x+d)*(x+1); hp=3*x**2+2*x-d*d
    J=-2*I; np.fill_diagonal(J,2*np.sum(I,axis=1)-5*hp/h); return J
def newton(x,d,w):
    for k in range(10):
        dx=np.linalg.solve(jac(x,d),-res(x,d,w)); x=x+dx
        if np.max(np.abs(dx)/(1+np.abs(x)))<1e-13: return x,True
    return x,np.max(np.abs(res(x,d,w)))<1e-9
def path(x,pa,pb):
    t=0; dt=1/steps
    while t<1:
        dt=min(dt,1-t); s=t+dt
        d=pa[0]+(pb[0]-pa[0])*s; w=pa[1]+(pb[1]-pa[1])*s
        xn,ok=newton(x,d,w)
        if ok and np.all(np.isfinite(xn)) and np.max(np.abs(xn-x)/(np.abs(xn)+0.05))<0.1: x=xn; t=s; dt*=1.5
        else:
            dt/=2
            if dt<1e-9: return None
    return x
fin=[]
for s in sols:
    y=path(s,(d0,w0),(dend,w0)); y=path(y,(dend,w0),(dend,wend)) if y is not None else None
    fin.append(y); print('sheet', None if y is None else np.round(np.sort_complex(y),4)[:3],flush=True)
mp.mp.dps=70
dm=mp.sqrt(mp.mpf(D2)) if D2>0 else mp.mpc(0,1)*mp.sqrt(-mp.mpf(D2))
if abs(complex(dm)-dend)>1e-6: dm=-dm
def polish(x):
    X=[mp.mpc(v.real,v.imag) for v in x]
    for it in range(12):
        R=[]; J=mp.matrix(9,9)
        for i in range(9):
            Fp=mp.mpf(1)
            for j in range(9):
                if j!=i: Fp*=X[i]-X[j]
            h=(X[i]-dm)*(X[i]+dm)*(X[i]+1)
            R.append(Fp**2-mp.mpf(C2)*h**5)
        # Jacobian by analytic formula on the polynomial form
        for i in range(9):
            Fp=mp.mpf(1)
            for j in range(9):
                if j!=i: Fp*=X[i]-X[j]
            h=(X[i]-dm)*(X[i]+dm)*(X[i]+1); hp=3*X[i]**2+2*X[i]-dm**2
            s=sum(1/(X[i]-X[j]) for j in range(9) if j!=i)
            for k in range(9):
                if k==i: J[i,k]=2*Fp**2*s-mp.mpf(C2)*5*h**4*hp
                else: J[i,k]=-2*Fp**2/(X[i]-X[k])
        dX=mp.lu_solve(J,-mp.matrix(R)); X=[X[i]+dX[i] for i in range(9)]
    return X, max(abs(r) for r in R)
E=[]
for y in fin:
    if y is None: continue
    X,r=polish(y); e=[mp.fsum(X), mp.fsum(X[i]*X[j] for i in range(9) for j in range(i))]
    E.append(e); print('polished resid %.1e'%float(r), 'e1', mp.nstr(e[0],20))
pickle.dump([(str(e[0].real),str(e[0].imag),str(e[1].real),str(e[1].imag)) for e in E],open('E_%s_%s.pkl'%(sys.argv[2],sys.argv[3]),'wb'))
for idx in [0,1]:
    T=[mp.mpf(1)]
    for e in E:
        T=[ (T[k] if k<len(T) else 0) - e[idx]*(T[k-1] if k>0 else 0) for k in range(len(T)+1)]
    print('resolvent e%d coefficients:'%(idx+1))
    for c in T: print('  ',mp.nstr(c.real,45),' im %.1e'%float(abs(c.imag)))
