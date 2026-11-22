"""Session 32: from a near-node endpoint (cross_log.py output), print the line's point norms and
try to cross u = 1/j through 0 linearly to +|u|*mult.  usage: python3 cross2.py <endpoint.npy> <mult> <nsteps>"""
import numpy as np, sys, warnings; warnings.filterwarnings('ignore')
exec(open('cross.py').read().split("ords = []")[0].replace("rows = np.load(sys.argv[1]); idx = int(sys.argv[2]); nst = int(sys.argv[3])",""))
from scipy.optimize import least_squares
v=np.load(sys.argv[1]); mult=float(sys.argv[2]); nst=int(sys.argv[3])
Z,a=v[:9],v[9:]; print('|Q_i| =',np.round(np.sort(np.hypot(Z,a)),5))
hc,x=weier(Z,a); r=np.roots(hc[::-1]); print('h roots',np.round(r,6),' x_i',np.round(np.sort(x),5))
u0=info(v)[0]; W=1/abs(u0)
for t in np.linspace(u0,-mult*u0,nst)[1:]:
    f=lambda w: np.r_[eqs(w), W*(info(w)[0]-t)]
    sol=least_squares(f,v,xtol=1e-15,ftol=1e-15,gtol=1e-15,max_nfev=600)
    res=np.abs(eqs(sol.x)).max(); u,par,nr,k=info(sol.x)
    print(f"target {t:+.3e}  u {u:+.3e}  res {res:.1e}  minpair {par:.2e}  h-real {nr}  k_egg {k}",flush=True)
    if res>1e-8: print('lost'); break
    v=sol.x
np.save(sys.argv[1][:-4]+'_x.npy',v)
