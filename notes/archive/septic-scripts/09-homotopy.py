# Phase 0: number of complex solutions of the decic square system, via a vectorized
# total-degree homotopy continuation (numpy).  No per-degree PSLQ, no CAS Groebner.
import numpy as np, sympy as sp, sys, time
from itertools import product
sys.stdout.reconfigure(line_buffering=True)

t,a,b,c,p,q,r,d = sp.symbols('t a b c p q r d')
vars7 = (a,b,c,p,q,r,d)
f = t**7 - 14*t**5 + 49*t**3 - 36*t + 1
u = t**3+a*t**2+b*t+c
up = sp.diff(u,t)
vq = p*t**2+q*t+r
cross = sp.expand(u**2*(up**2+vq**2) - d*vq**2)
rem = sp.rem(sp.Poly(cross,t), sp.Poly(f,t)).as_expr()
eqs = [sp.expand(e) for e in sp.Poly(rem, t).all_coeffs()]
degs = [sp.Poly(e, vars7).total_degree() for e in eqs]
print("equation total degrees:", degs, flush=True)
Dtot = int(np.prod(degs)); print("total degree bound:", Dtot, flush=True)

Ff = sp.lambdify(vars7, eqs, 'numpy')
Jac = sp.Matrix(eqs).jacobian(vars7)
Jflat = [sp.expand(Jac[i,j]) for i in range(7) for j in range(7)]
Jf = sp.lambdify(vars7, Jflat, 'numpy')

def F(Z):
    out = Ff(*[Z[:,i] for i in range(7)])
    return np.stack([np.broadcast_to(np.asarray(o, dtype=complex), Z.shape[0]) for o in out], axis=1)

def J(Z):
    ent = Jf(*[Z[:,i] for i in range(7)])
    M = np.empty((Z.shape[0],7,7), dtype=complex)
    for k in range(49):
        M[:, k//7, k%7] = np.broadcast_to(np.asarray(ent[k], dtype=complex), Z.shape[0])
    return M

# start system G_i = z_i^{d_i} - 1
roots = [np.array([np.exp(2j*np.pi*k/degs[i]) for k in range(degs[i])]) for i in range(7)]
Z = np.array(list(product(*roots)), dtype=complex)
N = Z.shape[0]; print("paths:", N, flush=True)

rng = np.random.default_rng(7)
gam = np.exp(2j*np.pi*rng.random())

def G(Z):
    return np.stack([Z[:,i]**degs[i] - 1 for i in range(7)], axis=1)
def JG(Z):
    M = np.zeros((Z.shape[0],7,7), dtype=complex)
    for i in range(7):
        M[:,i,i] = degs[i]*Z[:,i]**(degs[i]-1)
    return M

active = np.ones(N, dtype=bool)
T = 0.0; dt = 0.05
steps = 0
t0 = time.time()
while T < 1 - 1e-12 and steps < 100000:
    steps += 1
    h = min(dt, 1.0-T)
    idx = np.where(active)[0]
    Zi = Z[idx]
    JH = gam*(1-T)*JG(Zi) + T*J(Zi)
    dHdt = -gam*G(Zi) + F(Zi)
    try:
        tang = np.linalg.solve(JH, -dHdt)
    except np.linalg.LinAlgError:
        dt /= 2; continue
    Zp = Zi + h*tang
    ok = np.ones(len(idx), dtype=bool)
    for it in range(6):
        H = gam*(1-(T+h))*G(Zp) + (T+h)*F(Zp)
        Jp = gam*(1-(T+h))*JG(Zp) + (T+h)*J(Zp)
        try:
            dz = np.linalg.solve(Jp, -H)
        except np.linalg.LinAlgError:
            ok[:] = False; break
        Zp = Zp + dz
        nrm = np.max(np.abs(dz), axis=1)
        ok = nrm < 1e-10
        if ok.all(): break
    big = np.max(np.abs(Zp), axis=1) > 1e6
    good = ok & ~big
    if good.mean() < 0.5 and h > 1e-5:
        dt = max(dt/2, 1e-5); continue
    newZ = Zi.copy(); newZ[good] = Zp[good]
    Z[idx] = newZ
    active[idx] = active[idx] & good
    T += h
    dt = min(dt*1.3, 0.2)
    if steps % 20 == 0:
        print("  T=%.3f active=%d dt=%.4f  (%.1fs)" % (T, active.sum(), dt, time.time()-t0), flush=True)

print("tracking done: steps=%d active=%d  (%.1fs)" % (steps, active.sum(), time.time()-t0), flush=True)
# endpoints
sol = Z[active]
res = np.max(np.abs(F(sol)), axis=1)
print("endpoint residual: max=%.2e  #<1e-6: %d" % (res.max() if len(res) else -1, int((res<1e-6).sum())), flush=True)
sol = sol[res < 1e-6]
# dedupe
keep = []
for s in sol:
    if all(np.max(np.abs(s-y)) > 1e-6 for y in keep):
        keep.append(s)
keep = np.array(keep)
print("distinct complex solutions:", len(keep), flush=True)
np.save(r"archived files/septic-scripts/complex-solutions.npy", keep)
