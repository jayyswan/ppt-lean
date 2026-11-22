# Session 45: for real conics A+Bk+Ck^2 in V_3 (r given), the signature of the trace form T on span(A,B,C)
# versus the real-root count of p4 on the conic.  Usage: python3 sig45.py <r> <starts> <seed>
import sys, numpy as np
exec(open('iso45.py').read().split("\ndef main")[0])
r, starts, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(seed)
def Tform(y1, y2):
    z1, z2 = cplx(y1, r), cplx(y2, r)
    return np.sum(np.real(z1[:r]*z2[:r])) + 2*np.sum(np.real(z1[r:]*z2[r:]))
stats = {}
for st in range(starts):
    G = rng.standard_normal((6, 27)); g = rng.standard_normal(6)
    res = least_squares(resid, rng.standard_normal(27), args=(r, 2, [1,2,3], G, g), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
    if not np.isfinite(np.linalg.norm(res.fun)) or np.linalg.norm(res.fun) > 1e-10: continue
    Ys = res.x.reshape(3, 9)
    if np.linalg.svd(Ys, compute_uv=False)[-1]/np.linalg.norm(Ys) < 1e-4: continue
    C = coord_polys(Ys, r)
    if nclasses(C) < r + (9-r)//2: continue
    Gm = np.array([[Tform(a, b) for b in Ys] for a in Ys])
    ev = np.linalg.eigvalsh(Gm); ev = ev/np.max(abs(ev))
    p4 = psum_poly(C, r, 4); rts = np.roots(p4[::-1])
    nre = int(np.sum(abs(rts.imag) < 1e-7*np.maximum(1, abs(rts))))
    sig = (int(np.sum(ev > 1e-8)), int(np.sum(ev < -1e-8)))
    stats.setdefault(sig, []).append(nre)
    print(st, 'sig', sig, 'p4 real roots', nre, flush=True)
print({k: (len(v), sorted(v)) for k, v in stats.items()})
