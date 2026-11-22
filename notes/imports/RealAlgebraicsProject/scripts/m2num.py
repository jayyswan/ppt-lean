# numerical lower bound for the M2 count: Newton from random complex starts on chi | Z^2 - R(1-R)(1+e-eR)^2
import numpy as np, sys
rng=np.random.default_rng(int(sys.argv[1])); starts=int(sys.argv[2])
tau=rng.normal(size=9)+1j*rng.normal(size=9)
V=np.vander(tau,4,increasing=True)
def F(x):
    z=x[:4]; q=x[4:8]; e=x[8]
    Z=V@z; R=V@q
    return Z**2-R*(1-R)*(1+e-e*R)**2
def J(x):
    z=x[:4]; q=x[4:8]; e=x[8]
    Z=V@z; R=V@q; S=1+e-e*R
    dR=-( (1-2*R)*S**2 + R*(1-R)*2*S*(-e) )
    de=-(R*(1-R)*2*S*(1-R))
    return np.hstack([2*Z[:,None]*V, dR[:,None]*V, de[:,None]])
sols=[]
for k in range(starts):
    x=rng.normal(size=9)+1j*rng.normal(size=9)
    ok=False
    for it in range(60):
        f=F(x)
        if np.linalg.norm(f)<1e-11: ok=True;break
        try: dx=np.linalg.solve(J(x),-f)
        except: break
        x=x+dx
        if np.linalg.norm(x)>1e6: break
    if ok and np.linalg.norm(x[5:8])>1e-4 and np.linalg.norm(x)<1e5 and np.linalg.svd(J(x),compute_uv=False)[-1]>1e-9:
        key=x.copy(); key[:4]*=np.sign(key[3].real) if key[3].real!=0 else 1
        if not any(np.linalg.norm(key-s)<1e-6 for s in sols): sols.append(key)
    if (k+1)%2000==0: print(k+1,len(sols),flush=True)
    if k==starts-1 or len(sols)>=int(sys.argv[3] if len(sys.argv)>3 else 10**9):
        break
for s in sols[:15]:
    sv=np.linalg.svd(J(s),compute_uv=False)
    print("sv min/max %.2e %.2e  e=%s q1=%s"%(sv[-1],sv[0],np.round(s[8],3),np.round(s[5],3)))
