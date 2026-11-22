# Session 17: monodromy count of the fibre of line -> m (Proposition S17.2). Needs mfibre_core.py in the cwd.
# Usage: python3 mono.py <seed> <rounds>. Prints the number of distinct solutions a at one m (lines = half).
# Session 17: degree of the fibre of  line -> m = ab  by monodromy (complex path tracking).
# H = {9 sum m^2 = (sum m)^2}. Unknown a in C^9 with normalisation h.a = 1 (b = m/a).
import numpy as np, sys, warnings
warnings.filterwarnings('ignore')
rng = np.random.default_rng(int(sys.argv[1]))
ROUNDS = int(sys.argv[2])
exec(open('mfibre_core.py').read())
x, m0 = random_line(rng)
h = rng.normal(size=9) + 1j*rng.normal(size=9)
S = [x[:9]/(h@x[:9]), x[9:]/(h@x[9:])]
w = rng.normal(size=9) + 1j*rng.normal(size=9)
def onH(m):  # move m along w to H, nearest root
    A = 9*(w*w).sum() - w.sum()**2; B = 2*(9*(m*w).sum() - m.sum()*w.sum()); C = 9*(m*m).sum() - m.sum()**2
    r = np.roots([A, B, C]); c = r[np.argmin(abs(r))]; return m + c*w
def track(a, ma, mb, steps=400):
    t, dt = 0.0, 1.0/steps
    while t < 1 - 1e-12:
        dt = min(dt, 1 - t)
        mn = onH(ma + (t+dt)*(mb - ma)) if True else None
        b = a.copy(); ok = False
        for _ in range(8):
            f = F(b, mn, h)
            try: d = np.linalg.solve(J(b, mn, h), -f)
            except Exception: break
            if not np.all(np.isfinite(d)): break
            b = b + d
            if np.linalg.norm(d) < 1e-12*np.linalg.norm(b): ok = True; break
        if ok and np.linalg.norm(b - a) < 0.1*np.linalg.norm(a):
            a = b; t += dt; dt *= 1.5
        else:
            dt /= 2
            if dt < 1e-9: return None
    return a
def same(u, v): return np.linalg.norm(u - v) < 1e-7*np.linalg.norm(u)
count_hist = []
for r in range(ROUNDS):
    m1 = onH(m0 + 0.7*(rng.normal(size=9) + 1j*rng.normal(size=9))*np.abs(m0).mean())
    m2 = onH(m0 + 0.7*(rng.normal(size=9) + 1j*rng.normal(size=9))*np.abs(m0).mean())
    new = []
    for a in list(S):
        p = track(a, m0, m1)
        if p is None: continue
        p = track(p, m1, m2)
        if p is None: continue
        p = track(p, m2, m0)
        if p is None: continue
        if np.linalg.norm(F(p, m0, h)) < 1e-8 and not any(same(p, s) for s in S + new): new.append(p)
    S += new
    # close under the swap a <-> b = m/a
    for a in list(S):
        b = m0/a; b = b/(h@b)
        if not any(same(b, s) for s in S): S.append(b)
    count_hist.append(len(S))
    print('round', r+1, 'solutions', len(S), flush=True)
print('lines over m0 (solutions/2):', len(S)/2)
