# node68.py -- session 68: node-line residual identity (S68.1), numerical check.
# A projective node of V_A over F: nu in A with nu^2 = d (scalar), Tr nu = 0.
# Over C: nu = sqrt(d) * (1 on S, -1 on S^c), |S| = 5.
# Claim: for v with Tr v = Tr(nu v^2) = Tr v^3 = 0 (v in Y_nu),
#   Tr(nu + k v)^5 = 5 k^4 Tr(nu v^4) + k^5 Tr(v^5)   (identically in k),
# so y = Tr(v^5) nu - 5 Tr(nu v^4) v lies on V_A = {Tr y = Tr y^3 = Tr y^5 = 0}.
# Usage: python3 node68.py [trials] [seed]
import sys, numpy as np
T = int(sys.argv[1]) if len(sys.argv) > 1 else 20
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)

def solve_Y(nu):
    # Newton for v in C^10 on Tr v = Tr(nu v^2) = Tr v^3 = 0 plus 6 random affine slices + scale
    n = 10
    L = rng.normal(size=(6, n)) + 1j*rng.normal(size=(6, n)); c = rng.normal(size=6) + 1j*rng.normal(size=6)
    v = rng.normal(size=n) + 1j*rng.normal(size=n)
    for it in range(200):
        F = np.concatenate([[v.sum(), (nu*v*v).sum(), (v**3).sum()], L@v - c, [0]])[:9]
        J = np.vstack([np.ones(n), 2*nu*v, 3*v*v, L])
        dv = np.linalg.lstsq(J, -F, rcond=None)[0]
        v = v + dv
        if np.linalg.norm(dv) < 1e-14*(1+np.linalg.norm(v)): break
    return v

worst = 0; ranks = []; nsq = []
for t in range(T):
    d = complex(rng.normal(), rng.normal()) if t % 2 else 1.0     # split (d=1) and nonsplit nodes
    S = rng.permutation(10)[:5]
    sig = -np.ones(10); sig[S] = 1
    nu = np.sqrt(d)*sig
    v = solve_Y(nu)
    res = max(abs(v.sum()), abs((nu*v*v).sum()), abs((v**3).sum()))
    # identity in k
    for k in [0.37+0.2j, -1.3, 2.1j]:
        lhs = ((nu + k*v)**5).sum()
        rhs = 5*k**4*(nu*v**4).sum() + k**5*(v**5).sum()
        worst = max(worst, abs(lhs-rhs)/(1+abs(lhs)))
    y = (v**5).sum()*nu - 5*(nu*v**4).sum()*v
    y = y/np.linalg.norm(y)
    tr = [abs((y**k).sum()) for k in (1, 3, 5)]
    worst = max(worst, max(tr), res)
    J = np.vstack([np.ones(10), 3*y**2, 5*y**4])
    s = np.linalg.svd(J, compute_uv=False)
    ranks.append(int((s > 1e-8*s[0]).sum()))
    sq = y**2
    nsq.append(len({(round(z.real, 6), round(z.imag, 6)) for z in sq}))
print("max residual (Y_nu, identity, traces of y):", worst)
print("Jacobian ranks of V at y (3 = smooth):", sorted(set(ranks)), " distinct y_i^2 values:", sorted(set(nsq)))
