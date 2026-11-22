import numpy as np, pickle, sys
from bl import *
Y0,c0,d=pickle.load(open('base.pkl','rb'))
s=complex(sys.argv[1]); Y=track(Y0,[c0+2*d,c0+s*d]) if False else None
Y2=track(Y0,[c0,c0+2*d]); Y=track(Y2,[c0+2*d,c0+s*d],h0=0.01)
def logD(Y):
    g=sheets(Y); return sum(2*np.log(abs(g[i]-g[j])) for i in range(9) for j in range(i+1,9))/np.log(10)
step=0.05
for it in range(40):
    f0=logD(Y); best=None
    for k in range(8):
        t=s+step*np.exp(2j*np.pi*k/8); Yt=track(Y,[c0+s*d,c0+t*d],h0=0.01)
        if Yt is None: continue
        f=logD(Yt)
        if best is None or f>best[0]: best=(f,t,Yt)
    if best is None: print('stuck'); break
    if best[0]>f0: f0,s,Y=best
    else: step/=2
    g=sheets(Y); a,b=ab(Y); P,Q,T=moments(a,b)
    print(it,'s=%.5f%+.5fi logD %.3f step %.4f max|g| %.3f detQ %.2e |P|max %.2f'%(s.real,s.imag,f0,step,abs(g).max(),abs(np.linalg.det(Q)),np.abs(np.stack([a,b])).max()),flush=True)
    if step<1e-4: break
pickle.dump((s,Y),open('climb.pkl','wb'))
