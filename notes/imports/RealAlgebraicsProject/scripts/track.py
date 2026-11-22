# Homotopy from the nodal fibre (h0 = x^2 (x+1), x = (1-rho^2)/rho^2) to smooth h = (x-d)(x+d)(x+1).
# Unknowns x_1..x_8, c2 (x_9 fixed). Equations e_i = 1 - c2 h(x_i)^5 / F'(x_i)^2.
# usage: python3 track.py <g> <d_end (complex, e.g. 0.3+0.2j)> <steps>  -> prints + pickles endpoint
import numpy as np, sys, pickle, warnings; warnings.filterwarnings('ignore')
import mpmath as mp
g=complex(sys.argv[1]); dend=complex(sys.argv[2]); steps=int(sys.argv[3])
O=np.array([0,-63,0,-84,0,126/5,0,-36/5,0,1.0]); E=np.array([64/5,0,576/5]+[0]*7)
rho=np.roots((O+g*E)[::-1]); x=(1-rho**2)/rho**2
def hfun(t,d): return (t-d)*(t+d)*(t+1)
def sysf(v,xfix,d):
    xx=np.concatenate([v[:8],[xfix]]); D=xx[:,None]-xx[None,:]; np.fill_diagonal(D,1)
    Fp=np.prod(D,axis=1); return 1-v[8]*hfun(xx,d)**5/Fp**2
D=x[:,None]-x[None,:]; np.fill_diagonal(D,1); Fp=np.prod(D,axis=1)
c2s=Fp**2/hfun(x,0)**5
print('nodal check: c2 constant across roots? spread %.2e' % (np.std(c2s)/abs(np.mean(c2s))))
v=np.concatenate([x[:8],[np.mean(c2s)]]).astype(complex); xfix=x[8]
def jac(v,d):
    f=sysf(v,xfix,d); J=np.zeros((9,9),complex)
    for k in range(9):
        w=v.copy(); h=1e-7*(1+abs(v[k])); w[k]+=h; J[:,k]=(sysf(w,xfix,d)-f)/h
    return f,J
ok=True
for s in range(1,steps+1):
    d=dend*s/steps
    for it in range(30):
        f,J=jac(v,d); dv=np.linalg.solve(J,-f); v=v+dv
        if np.linalg.norm(dv)<1e-13*(1+np.linalg.norm(v)): break
    if not np.all(np.isfinite(v)) or np.linalg.norm(sysf(v,xfix,d))>1e-9: ok=False; print('lost at step',s); break
if ok:
    xx=np.concatenate([v[:8],[xfix]])
    print('end residual %.1e, min sep %.2e' % (np.linalg.norm(sysf(v,xfix,dend)), min(abs(xx[i]-xx[j]) for i in range(9) for j in range(i))))
    pickle.dump((dend,xx,v[8]),open('track_end.pkl','wb'))
