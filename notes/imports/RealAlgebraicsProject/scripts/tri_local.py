# Session 35: large-K limit of the m=6 core: 3 points s_k near a 2-torsion point, local problem
#   prod_{j!=k} (s_k - s_j)^2 = C * s_k^5   (scale-free: C can be normalised to +1 or -1, or any unit complex).
# All complex solutions for C = 1 (up to permutation); real forms reachable: s real, s>0 (two-component side, t=1+delta, delta>0).
import numpy as np
rng=np.random.default_rng(1)
def wrap(z): return z.real+1j*((z.imag+np.pi)%(2*np.pi)-np.pi)
sols=[]
for C in [1.0,-1.0]:
  found=[]
  for _ in range(4000):
    s=(rng.normal(size=3)+1j*rng.normal(size=3))
    for it in range(100):
        D=s[:,None]-s[None,:]; np.fill_diagonal(D,1)
        R=wrap(2*np.log(D).sum(1)-5*np.log(s)-np.log(C+0j))
        iD=1/D; np.fill_diagonal(iD,0)
        J=-2*iD; np.fill_diagonal(J,2*iD.sum(1)-5/s)
        try: ds=np.linalg.solve(J,R)
        except: break
        sc=min(1,0.3*np.min(np.abs(s))/max(np.abs(ds).max(),1e-300)); s=s-sc*ds
    D=s[:,None]-s[None,:]; np.fill_diagonal(D,1)
    R=wrap(2*np.log(D).sum(1)-5*np.log(s)-np.log(C+0j))
    if np.abs(R).max()<1e-11 and np.abs(D).min()>1e-6:
        c=np.sort_complex(s)
        if not any(np.allclose(c,q,atol=1e-8) for q in found): found.append(c)
  print("C=",C,"distinct solutions:",len(found))
  for c in found:
      tag = "REAL all>0" if (np.abs(c.imag).max()<1e-9 and (c.real>0).all()) else ("real mixed" if np.abs(c.imag).max()<1e-9 else "")
      print("   ",np.round(c,5),tag)
