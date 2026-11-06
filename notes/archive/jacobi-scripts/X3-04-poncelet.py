# X3-04-poncelet.py -- Poncelet/Jacobi for two circles.
# Outer unit circle O=(0,0); inner circle C=(d,0) radius r, r+d<1.
# From P=e^{i theta} a tangent chord touches the inner circle and meets the outer
# circle again at P'=e^{i theta'}.  With chord-normal angle psi:
#     chord line n.X=n.P, n=(cos psi,sin psi); its circle intersections have angles
#     psi +/- arccos(n.P), and one is theta, so theta' = 2 psi - theta;
#     tangency  n.(C-P) = s r  (s=+/-1).   Hence theta' solves a quadratic in tan(psi/2):
#     the map is ALGEBRAIC of degree 2 (not a Mobius rotation).
# Jacobi: for the right modulus m, F(theta',m) - F(theta,m) is a constant step Delta.
import mpmath as mp
from mpmath import mpf, sqrt, sin, cos, atan2, pi, acos

mp.mp.dps = 30

def candidates(theta, r, d):
    A = d - cos(theta); B = -sin(theta)          # (d-cos t, -sin t) = C-P
    R = sqrt(A*A + B*B); base = atan2(B, A); out = []
    for s in (1, -1):
        val = s*r/R
        if abs(val) > 1: continue
        al = acos(val)
        for psi in (base+al, base-al):
            tp = (2*psi - theta) % (2*pi)
            if all(abs((tp-t) % (2*pi)) > mpf('1e-9') and
                   abs((tp-t) % (2*pi) - 2*pi) > mpf('1e-9') for t in out):
                out.append(tp)
    return out

def orbit(r, d, N=22):
    ths = [mpf(0)]
    c0 = sorted(candidates(mpf(0), r, d))
    ths.append(c0[0])                             # forward branch at theta=0
    while len(ths) < N:
        cs = candidates(ths[-1], r, d); prev = ths[-2]
        nxt = [t for t in cs
               if abs((t-prev) % (2*pi)) > mpf('1e-6') and
                  abs((t-prev) % (2*pi) - 2*pi) > mpf('1e-6')]
        if not nxt: break
        ths.append(nxt[0])
    # unwrap to increasing
    un = [ths[0]]
    for x in ths[1:]:
        while x < un[-1] - mpf('1e-9'): x += 2*pi
        un.append(x)
    return un

def fit_step(un, mvals):
    best = None
    for m in mvals:
        F = [mp.ellipf(t, m) for t in un]
        vals = [F[n+1]-F[n] for n in range(len(F)-1)]
        mean = sum(vals)/len(vals)
        sp = max(abs(v-mean) for v in vals)
        if best is None or sp < best[0]: best = (sp, m, mean)
    return best

for (r, d) in [(mpf('0.4'), mpf('0.3')), (mpf('0.25'), mpf('0.5'))]:
    un = orbit(r, d)
    print("r,d = %s,%s   first thetas: %s" %
          (r, d, ", ".join(mp.nstr(x, 7) for x in un[:7])))
    best = fit_step(un, [mpf(j)/500 for j in range(1, 500)])
    print("   best Jacobi fit: m = %s   step Delta = %s   spread = %.2e"
          % (mp.nstr(best[1], 12), mp.nstr(best[2], 15), best[0]))
    # refine m
    m = best[1]
    for _ in range(4):
        cand = [m + (mpf(k)-20)/mpf(500)/mpf(20) for k in range(41)]
        b2 = fit_step(un, [x for x in cand if 0 < x < 1])
        if b2[0] < best[0]: best = b2; m = b2[1]
    print("   refined:        m = %s   step Delta = %s   spread = %.2e"
          % (mp.nstr(best[1], 15), mp.nstr(best[2], 18), best[0]))
    print("   => F(theta',m) = F(theta,m) + Delta  (%s)" %
          ("conjugacy holds" if best[0] < 1e-20 else "not confirmed"))

# (C) prescribing the step = inverting F, i.e. reconstructing am
print("\n(C) Delta depends transcendentally on r,d; making Delta = u needs an F-inverse.")
r0, d0 = mpf('0.4'), mpf('0.3')
un0 = orbit(r0, d0)
m0 = best[1]   # last fitted modulus (for second pair); recompute for clarity
m0 = fit_step(un0, [mpf(j)/500 for j in range(1, 500)])[1]
def Delta_of_r(rr):
    u = orbit(rr, d0, N=18)
    b = fit_step(u, [m0])
    return b[2]
for u in [mpf('0.5'), mpf('0.9')]:
    lo, hi = mpf('0.05'), mpf('0.62')
    for _ in range(70):
        mid = (lo+hi)/2
        try:
            if Delta_of_r(mid) < u: lo = mid
            else: hi = mid
        except Exception: hi = (lo+hi)/2
    print("   target step u=%s -> r=%s" % (u, mp.nstr((lo+hi)/2, 10)))
print("   the relation Delta(r)=u is non-algebraic in r; its solution is am(u)-like.")
