# real solutions of the M2 system for a generator with r real conjugates (r = 1,3,5,7,9): real Newton from real starts
import numpy as np, sys
exec(open('m2num.py').read().split("sols=[]")[0].replace("V=np.vander(tau,4,increasing=True)",""))
r=int(sys.argv[3]); s=(9-r)//2
re_=np.sort(rng.normal(size=r)); cz=rng.normal(size=s)+1j*np.abs(rng.normal(size=s))+0.3j
tau=np.concatenate([re_,cz,np.conj(cz)]); V=np.vander(tau,4,increasing=True)
sols=[]
for k in range(int(sys.argv[2])):
    x=rng.normal(size=9).astype(complex)*rng.choice([0.3,1,3])
    ok=False
    for it in range(80):
        f=F(x)
        if np.linalg.norm(f)<1e-11: ok=True;break
        try: dx=np.linalg.solve(J(x),-f)
        except: break
        x=x+dx; x=x.real+0j
        if np.linalg.norm(x)>1e6: break
    if ok and np.linalg.norm(x[5:8])>1e-4 and np.linalg.svd(J(x),compute_uv=False)[-1]>1e-9:
        key=x.real.copy(); key[:4]*=np.sign(key[3]) if key[3]!=0 else 1
        if not any(np.linalg.norm(key-s_)<1e-6 for s_ in sols): sols.append(key)
print("r =",r,"distinct real nondegenerate solutions (mod Z sign):",len(sols))
print("e values:", sorted(round(float(x[8]),3) for x in sols))
for x in sols[:0]:
    R=(np.vander(re_,4,increasing=True)@x[4:8]); print(" e=%.4f  r_j at real tau in [0,1]:"%x[8], np.all((R>=-1e-9)&(R<=1+1e-9)))
