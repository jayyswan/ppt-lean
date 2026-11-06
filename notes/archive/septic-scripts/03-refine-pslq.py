# Phase 0: refine the real solution of the square system to high precision and run
# PSLQ for minimal polynomials of every coordinate, under the strict rule
#     (d+1) * log10(H) <= digits/2,  and re-verify at twice the precision.
# Usage:  03-refine-pslq.py [max_dps] [pslq_dps]
import mpmath as mp
import numpy as np, sys, pickle, os

sys.stdout.reconfigure(line_buffering=True)
HERE = os.path.dirname(os.path.abspath(__file__))
seed = np.load(os.path.join(HERE, "seed-solution.npy"))
print("seed:", seed, flush=True)

def f(t):  return t**7 - 14*t**5 + 49*t**3 - 36*t + 1
def fp(t): return 7*t**6 - 70*t**4 + 147*t**2 - 36

def high_roots(dps):
    mp.mp.dps = dps + 30
    seedr = np.roots([1,0,-14,0,49,0,-36,1]).real
    rts = []
    for x0 in seedr:
        x = mp.mpf(repr(float(x0)))
        for _ in range(300):
            dx = f(x)/fp(x)
            x = x - dx
            if abs(dx) < mp.mpf(10)**(-(dps+10)):
                break
        rts.append(x)
    return sorted(rts)

def residual(z, rts):
    a,b,c,p,q,rr,D = z
    out = []
    for t in rts:
        u = t**3 + a*t**2 + b*t + c
        up = 3*t**2 + 2*a*t + b
        vp = 2*p*t + q
        vv = p*t**2 + q*t + rr
        out.append(((u*u)*(up*up+vp*vp)) - D*vv*vv)
    return mp.matrix(out)

def jacobian(z, rts):
    a,b,c,p,q,rr,D = z
    J = mp.zeros(7,7)
    for i,t in enumerate(rts):
        u = t**3 + a*t**2 + b*t + c
        up = 3*t**2 + 2*a*t + b
        vp = 2*p*t + q
        vv = p*t**2 + q*t + rr
        S = up*up+vp*vp
        J[i,0] = 2*u*(t**2)*S + u*u*(2*up*(2*t))
        J[i,1] = 2*u*(t)*S + u*u*(2*up)
        J[i,2] = 2*u*S
        J[i,3] = u*u*(2*vp*(2*t)) - D*(2*vv*(t*t))
        J[i,4] = u*u*(2*vp) - D*(2*vv*t)
        J[i,5] = -D*(2*vv)
        J[i,6] = -vv*vv
    return J

def refine(z, dps):
    mp.mp.dps = dps + 60
    rts = high_roots(dps+60)
    z = [mp.mpf(x) for x in z]
    nrm = mp.mpf(1)
    for it in range(80):
        F = residual(z, rts)
        nrm = max(abs(v) for v in F)
        if nrm < mp.mpf(10)**(-(dps+30)):
            break
        J = jacobian(z, rts)
        dz = mp.lu_solve(J, F)
        z = [z[k] - dz[k] for k in range(7)]
    return z, nrm, it

z = [mp.mpf(repr(float(x))) for x in seed]
for dps in [80, 300, 1000, 3000, 6000]:
    z, nrm, it = refine(z, dps)
    with open(os.path.join(HERE, f"z-{dps}.pkl"), "wb") as fh:
        pickle.dump([mp.nstr(x, dps+40) for x in z], fh)
    print("dps=%5d it=%2d max|F|=%.3e Delta=%s" % (dps, it, float(nrm), mp.nstr(z[6],20)), flush=True)
