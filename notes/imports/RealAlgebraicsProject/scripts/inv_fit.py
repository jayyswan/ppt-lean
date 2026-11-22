"""Session 34: residue-type invariant test on curves in L_135.
For curves z_i(t) = Q_i(t) (binary forms of degree DEG in t, coefficient rows
Q_i), compute per-index invariants
  D_i = discriminant of Q_i (DEG = 2) or 1 (DEG = 1)
  T_i = prod_{j != i} Res(Q_i, Q_j)
  U_i = prod_{j != i} B(Q_i, Q_j)   (B = polarised discriminant; DEG = 2)
and test whether v_i = T_i^p D_i^q U_i^r equals Phi(Q_i)/Psi(Q_i) with Phi, Psi
forms of small degree in the coefficients (a linear kernel test, 9 equations).
For lines (DEG = 1) the S29.1 criterion predicts T_i = const * ell(L_i)^2,
i.e. (p,q,r) = (1,0,0) with Phi of degree 2 of rank one.
Usage: inv_fit.py <file.npy> <DEG> [labels.npy]
Prints, for each (p,q,r,dPhi,dPsi), the median and max over samples of the
relative smallest singular value, sorted."""
import numpy as np, itertools, sys
f = sys.argv[1]; DEG = int(sys.argv[2])
Qs = np.load(f)
if len(sys.argv) > 3:
    lab = np.load(sys.argv[3]); Qs = Qs[lab == 'gen']
n = 9

def res(a, b):
    if DEG == 1:
        return a[0]*b[1] - a[1]*b[0]
    a0, a1, a2 = a; b0, b1, b2 = b
    return (a0*b2 - a2*b0)**2 - (a0*b1 - a1*b0)*(a1*b2 - a2*b1)
def disc(a):
    return 1.0 if DEG == 1 else a[1]**2 - 4*a[0]*a[2]
def bil(a, b):
    return 1.0 if DEG == 1 else a[1]*b[1] - 2*(a[0]*b[2] + a[2]*b[0])

def monos(Q, d):
    k = Q.shape[1]
    es = [e for e in itertools.product(range(d + 1), repeat=k) if sum(e) == d]
    return np.array([[np.prod(q**np.array(e)) for e in es] for q in Q])

def invariants(Q):
    Q = Q / np.linalg.norm(Q, axis=1).mean()
    T = np.array([np.prod([res(Q[i], Q[j]) for j in range(n) if j != i]) for i in range(n)])
    D = np.array([disc(Q[i]) for i in range(n)])
    U = np.array([np.prod([bil(Q[i], Q[j]) for j in range(n) if j != i]) for i in range(n)])
    return Q, T, D, U

def test(Q, v, dphi, dpsi):
    A = monos(Q, dphi); B = monos(Q, dpsi) * v[:, None]
    M = np.hstack([A, -B])
    if M.shape[1] >= n: return None
    W = 1 / (np.linalg.norm(A, axis=1) + np.linalg.norm(B, axis=1))
    _, s, vt = np.linalg.svd(M * W[:, None])
    x = vt[-1]
    a = A @ x[:A.shape[1]]; b = B @ x[A.shape[1]:]
    with np.errstate(all='ignore'):
        dev = np.abs(np.log(np.abs(a)) - np.log(np.abs(b)))
    dev[~np.isfinite(dev)] = 99
    return dev.max()   # 0 = exact relation v_i = Phi(Q_i)/Psi(Q_i) at every i

if __name__ == '__main__':
    rows = {}
    pr = range(-2, 3); qr = range(-4, 5) if DEG == 2 else [0]; rr = range(-2, 3) if DEG == 2 else [0]
    shapes = [(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (0, 2), (2, 1)] if DEG == 2 else \
             [(0, 0), (1, 0), (2, 0), (3, 0), (0, 1), (1, 1), (2, 1), (0, 2), (1, 2), (2, 2), (3, 1)]
    for Q in Qs:
        Q, T, D, U = invariants(Q)
        for p, q, r in itertools.product(pr, qr, rr):
            if p == 0 and r == 0: continue   # D alone is trivially a quadric
            v = T**p * D**q * U**r
            v = v / np.abs(v).max()
            for dphi, dpsi in shapes:
                t = test(Q, v, dphi, dpsi)
                if t is None: continue
                rows.setdefault((p, q, r, dphi, dpsi), []).append(t)
    out = sorted(((np.median(v), np.max(v), k) for k, v in rows.items()))
    print('samples', len(Qs))
    for med, mx, k in out[:25]:
        print(k, 'median %.2e max %.2e' % (med, mx))
