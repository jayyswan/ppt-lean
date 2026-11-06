# Phase 0: refine every real solution of the CORRECT system and determine the honest
# degree of each coordinate.  Strict rule: (d+1) log10 H <= digits/2, enforced as a
# hard maxcoeff bound; a returned relation is therefore admissible.
# Usage: 04-all-pslq.py [dps] [maxdeg]
import mpmath as mp
import numpy as np, sys, os, json
sys.stdout.reconfigure(line_buffering=True)
HERE = os.path.dirname(os.path.abspath(__file__))
sols = np.load(os.path.join(HERE, "all-solutions.npy"))
print("loaded", len(sols), "solutions")

def f(t):  return t**7 - 14*t**5 + 49*t**3 - 36*t + 1
def fp(t): return 7*t**6 - 70*t**4 + 147*t**2 - 36

def high_roots(dps):
    mp.mp.dps = dps + 40
    seedr = np.roots([1,0,-14,0,49,0,-36,1]).real
    rts=[]
    for x0 in seedr:
        x=mp.mpf(repr(float(x0)))
        for _ in range(400):
            dx=f(x)/fp(x); x=x-dx
            if abs(dx)<mp.mpf(10)**(-(dps+20)): break
        rts.append(x)
    return sorted(rts)

def residual(z, rts):
    a,b,c,p,q,rr,D = z
    out = []
    for t in rts:
        u = t**3 + a*t**2 + b*t + c
        up = 3*t**2 + 2*a*t + b
        vq = p*t**2 + q*t + rr
        out.append(u*u*(up*up+vq*vq) - D*vq*vq)
    return mp.matrix(out)

def jacobian(z, rts):
    a,b,c,p,q,rr,D = z
    J = mp.zeros(7,7)
    for i,t in enumerate(rts):
        u = t**3 + a*t**2 + b*t + c
        up = 3*t**2 + 2*a*t + b
        vq = p*t**2 + q*t + rr
        S = up*up + vq*vq
        J[i,0] = 2*u*t*t*S + u*u*(4*up*t)
        J[i,1] = 2*u*t*S + u*u*(2*up)
        J[i,2] = 2*u*S
        J[i,3] = 2*(u*u-D)*vq*t*t
        J[i,4] = 2*(u*u-D)*vq*t
        J[i,5] = 2*(u*u-D)*vq
        J[i,6] = -vq*vq
    return J

def refine(z, dps):
    mp.mp.dps = dps + 60
    rts = high_roots(dps+60)
    z = [mp.mpf(x) for x in z]
    nrm = mp.mpf(1)
    for it in range(150):
        F = residual(z, rts)
        nrm = max(abs(v) for v in F)
        if nrm < mp.mpf(10)**(-(dps+30)): break
        dz = mp.lu_solve(jacobian(z, rts), F)
        z = [z[k] - dz[k] for k in range(7)]
    return z, nrm

def pslq_deg(x, dps, maxdeg=12):
    for d in range(1, maxdeg+1):
        maxc = 10**(dps // (2*(d+1)))
        rel = mp.pslq([x**j for j in range(d+1)], tol=mp.mpf(10)**(-(dps*3//4)),
                      maxcoeff=maxc, maxsteps=10**6)
        if rel:
            H = max(abs(int(v)) for v in rel)
            val = abs(sum(int(c)*x**j for j,c in enumerate(rel)))
            if (d+1)*mp.log10(H) <= mp.mpf(dps)/2 and val < mp.mpf(10)**(-(dps*2//3)):
                return (d, int(H), val, [int(v) for v in rel])
    return None

names = ['a','b','c','p','q','r','Delta']
DPS = int(sys.argv[1]) if len(sys.argv)>1 else 1000
MAXDEG = int(sys.argv[2]) if len(sys.argv)>2 else 12
out = {}
for si, s in enumerate(sols):
    z, nrm = refine(s, DPS)
    print("\n### solution %d  max|F|=%.2e  Delta=%s" % (si, float(nrm), mp.nstr(z[6],20)), flush=True)
    out[si] = []
    for k in range(7):
        b = pslq_deg(z[k], DPS, maxdeg=MAXDEG)
        if b:
            d,H,val,rel = b
            print("  %-5s deg=%2d log10H=%6.1f |p(x)|=%.2e" %
                  (names[k], d, float(mp.log10(H)), float(val)), flush=True)
            out[si].append((names[k], d, float(mp.log10(H)), rel))
        else:
            print("  %-5s no relation d<=%d" % (names[k], MAXDEG), flush=True)
    # save refinement for later
    with open(os.path.join(HERE, "refined-%d.pkl" % si), "wb") as fh:
        import pickle; pickle.dump([mp.nstr(x, DPS+40) for x in z], fh)
with open(os.path.join(HERE, "pslq-results.json"), "w") as fh:
    json.dump(out, fh)
print("\ndone")
