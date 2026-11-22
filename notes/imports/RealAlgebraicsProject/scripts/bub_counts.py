# Session 35: convergence rates and distinct complex solution counts of the bubble problem for m = 4..8 (execs header of cbubble.py; ~2 min)
import numpy as np, sys
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
rng=np.random.default_rng(5)
for m in [4,5,6,7,8]:
  for K in [1.0,-1.0,0.1,-0.1,10.0]:
    T0=(rng.normal(size=(3000,m))+1j*rng.normal(size=(3000,m)))*np.exp(rng.uniform(-1.5,1.5,(3000,m)))
    T,res=newton(T0,K,iters=150)
    good=np.isfinite(res)&(res<1e-10)
    sols=all_solutions(m,K,1000,rng,rounds=4)
    real=[s for s in sols if np.abs(s.imag).max()<1e-8]; im=[s for s in sols if np.abs(s.real).max()<1e-8]
    print(m,K,"conv frac",good.mean().round(3),"distinct",len(sols),"real",len(real),"imag",len(im),flush=True)
    for s in im: print("    imag v:",np.round(np.sort(s.imag),4))
