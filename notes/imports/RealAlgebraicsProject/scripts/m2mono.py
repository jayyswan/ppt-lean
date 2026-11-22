# S58: monodromy solve for the M2 fixed-generator scheme (Bezier x egg, S57.1)
# unknowns x = (z0..z3, q0..q3, e); equations F(tau_j) = Z(tau_j)^2 - R(1-R)(1+e-eR)^2 = 0, j = 1..9
# parameters: the 9 roots tau (a generic complex generator); loops tau0 -> tau1 -> tau2 -> tau0 (random tau1, tau2)
# usage: python3 m2mono.py <seed> <loops> [out.pkl]
import numpy as np, sys, pickle, time, os
HMAX = float(os.environ.get('HMAX', '0.05'))
rng = np.random.default_rng(int(sys.argv[1])); NL = int(sys.argv[2])
out = sys.argv[3] if len(sys.argv) > 3 else f"m2mono_{sys.argv[1]}.pkl"

def V(t): return np.vander(t, 4, increasing=True)
def Fv(x, t):
    z, q, e = x[:4], x[4:8], x[8]; A = V(t); Z = A @ z; R = A @ q; S = 1 + e - e*R
    return Z**2 - R*(1-R)*S**2
def Jx(x, t):
    z, q, e = x[:4], x[4:8], x[8]; A = V(t); Z = A @ z; R = A @ q; S = 1 + e - e*R
    dR = -((1-2*R)*S**2 - 2*e*R*(1-R)*S); de = -(2*R*(1-R)*S*(1-R))
    return np.hstack([2*Z[:, None]*A, dR[:, None]*A, de[:, None]])
def Ft(x, t):  # d/dt of F at t (per root)
    z, q, e = x[:4], x[4:8], x[8]; A = V(t); Z = A @ z; R = A @ q; S = 1 + e - e*R
    dA = np.stack([np.zeros_like(t), np.ones_like(t), 2*t, 3*t**2], 1)
    Zp = dA @ z; Rp = dA @ q
    dFdR = -((1-2*R)*S**2 - 2*e*R*(1-R)*S)
    return 2*Z*Zp + dFdR*Rp

def newton(x, t, tol=1e-12, it=8):
    for _ in range(it):
        f = Fv(x, t)
        dx = np.linalg.solve(Jx(x, t), -f); x = x + dx
        if np.linalg.norm(dx) < tol*(1+np.linalg.norm(x)): return x, True
    return x, np.linalg.norm(Fv(x, t)) < 1e-10

def track(x, ta, tb):
    s, h = 0.0, 0.02
    dt = tb - ta
    while s < 1:
        h = min(h, 1-s)
        t0 = ta + s*dt
        try:
            v = -np.linalg.solve(Jx(x, t0), Ft(x, t0)*dt)   # dx/ds
            # RK4 predictor
            def vel(xx, ss):
                tt = ta + ss*dt; return -np.linalg.solve(Jx(xx, tt), Ft(xx, tt)*dt)
            k1 = v; k2 = vel(x+h/2*k1, s+h/2); k3 = vel(x+h/2*k2, s+h/2); k4 = vel(x+h*k3, s+h)
            xp = x + h/6*(k1+2*k2+2*k3+k4)
            t1 = ta + (s+h)*dt
            ok = True; y = xp
            for i in range(4):
                dy = np.linalg.solve(Jx(y, t1), -Fv(y, t1)); y = y + dy
                if i == 0: d0 = np.linalg.norm(dy)
                if i == 1 and np.linalg.norm(dy) > 0.25*d0 + 1e-14: ok = False; break
            if ok and np.linalg.norm(y - xp) < 0.05*(1+np.linalg.norm(x)) and np.isfinite(y).all():
                x = y; s += h; h = min(HMAX, h*1.5)
            else:
                h /= 2
                if h < 1e-7: return None
        except np.linalg.LinAlgError:
            h /= 2
            if h < 1e-7: return None
        if np.linalg.norm(x) > 1e7: return None
    x, ok = newton(x, tb)
    return x if ok else None

def good(x, t):
    return np.isfinite(x).all() and np.linalg.norm(x[5:8]) > 1e-5 and np.linalg.norm(x) < 1e6 and \
        np.linalg.svd(Jx(x, t), compute_uv=False)[-1] > 1e-10
def find(S, x, tol=1e-7):
    A = np.array(S); d = np.linalg.norm(A - x, axis=1)
    i = int(np.argmin(d))
    return i if d[i] < tol*(1+np.linalg.norm(x)) else -1

# seed: random dials, tau0 = 9 of the 12 roots of F
x0 = rng.normal(size=9) + 1j*rng.normal(size=9)
z, q, e = x0[:4], x0[4:8], x0[8]
Zp = np.polynomial.Polynomial(z); Rp = np.polynomial.Polynomial(q)
Fp = Zp**2 - Rp*(1-Rp)*(1+e-e*Rp)**2
rts = Fp.roots(); tau0 = rts[rng.permutation(12)[:9]]
x0, ok = newton(x0, tau0); assert ok and good(x0, tau0)
S = [x0, x0*np.array([-1]*4+[1]*5)]
perms = []
if len(sys.argv) > 4:   # resume: python3 m2mono.py <seed> <loops> <out> <resume.pkl>; old loops are not kept
    tau0, S, perms = pickle.load(open(sys.argv[4], 'rb')); S = list(S); perms = []
T0 = time.time()
for L in range(NL):
    t1 = rng.normal(size=9)+1j*rng.normal(size=9); t2 = rng.normal(size=9)+1j*rng.normal(size=9)
    t1 = tau0 + 1.0*(t1); t2 = tau0 + 1.0*(t2)
    img = []; fails = 0
    for x in list(S):
        y = track(x, tau0, t1)
        if y is not None: y = track(y, t1, t2)
        if y is not None: y = track(y, t2, tau0)
        if y is None or not good(y, tau0): img.append(-1); fails += 1; continue
        j = find(S, y)
        if j < 0: S.append(y); j = len(S)-1
        img.append(j)
    from collections import Counter
    cnt = Counter(j for j in img if j >= 0)
    img = [(-1 if (j >= 0 and cnt[j] > 1) else j) for j in img]   # collisions = path jumps: drop both
    perms.append(img)
    print(f"loop {L+1}: |S| = {len(S)}, fails {fails}, time {time.time()-T0:.0f}s", flush=True)
    pickle.dump((tau0, S, perms), open(out, 'wb'))
