# Phase 0 step 1: real solutions of the (correct) square covering system
#   u  = t^3+a t^2+b t+c
#   vq = p t^2+q t+r          (v', the quadratic)
#   up = 3t^2+2at+b
#   F_i = u(r_i)^2 (up(r_i)^2+vq(r_i)^2) - Delta vq(r_i)^2 = 0, i=1..7
# for f = t^7 - 14 t^5 + 49 t^3 - 36 t + 1.
import numpy as np, sys
from scipy.optimize import root

fcoef = [1, 0, -14, 0, 49, 0, -36, 1]

def roots_double():
    return np.sort(np.roots(fcoef).real)

def make_res_jac(r):
    r = np.array(r, dtype=float)
    def res(z):
        a,b,c,p,q,rr,D = z
        out = np.empty(7)
        for i,t in enumerate(r):
            u = t**3 + a*t**2 + b*t + c
            up = 3*t**2 + 2*a*t + b
            vq = p*t**2 + q*t + rr
            out[i] = u*u*(up*up+vq*vq) - D*vq*vq
        return out
    def jac(z):
        a,b,c,p,q,rr,D = z
        J = np.zeros((7,7))
        for i,t in enumerate(r):
            u = t**3 + a*t**2 + b*t + c
            up = 3*t**2 + 2*a*t + b
            vq = p*t**2 + q*t + rr
            S = up*up+vq*vq
            J[i,0] = 2*u*(t**2)*S + u*u*(4*up*t)
            J[i,1] = 2*u*t*S + u*u*(2*up)
            J[i,2] = 2*u*S
            J[i,3] = 2*(u*u-D)*vq*(t*t)
            J[i,4] = 2*(u*u-D)*vq*t
            J[i,5] = 2*(u*u-D)*vq
            J[i,6] = -vq*vq
        return J
    return res, jac

rng = np.random.default_rng(20240913)
r = roots_double()
res, jac = make_res_jac(r)
print("roots of f:", r)

sols = []
for trial in range(20000):
    z0 = np.array([rng.uniform(-6,6), rng.uniform(-12,12), rng.uniform(-10,10),
                   rng.uniform(-3,3), rng.uniform(-12,12), rng.uniform(-12,12),
                   10**rng.uniform(-1,3)])
    try:
        s = root(res, z0, jac=jac, method='hybr', options={'maxfev':6000})
    except Exception:
        continue
    if not s.success:
        continue
    rn = np.linalg.norm(res(s.x))
    if rn < 1e-9:
        if all(np.linalg.norm(s.x - y) > 1e-4 for y in sols):
            sols.append(s.x.copy())
print("distinct real solutions (any Delta):", len(sols))
pos = [s for s in sols if s[6] > 1e-6]
print("distinct real solutions with Delta>0:", len(pos))
for s in sols:
    print("  Delta=%12.7f  a=%8.5f b=%8.5f c=%8.5f p=%8.5f q=%8.5f r=%8.5f  |res|=%.2e"
          % (s[6], s[0],s[1],s[2],s[3],s[4],s[5], np.linalg.norm(res(s))))
np.save(r"archived files/septic-scripts/all-solutions.npy", np.array(sols))
print("saved", len(sols), "solutions")
