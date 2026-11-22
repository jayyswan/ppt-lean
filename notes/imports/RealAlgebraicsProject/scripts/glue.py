# Session 35: build real S_ord lines near the nodal fibre from the asymptotic picture
#   core: unique m=6 bubble (t_i), outer: 3 points with charge +1 at the node,
# glue x = beta*t (core) + outer x_k, h = (x+1)(x^2+beta^2), Newton on the full criterion
#   V_i = sum_{j!=i} log|x_i-x_j| - 2.5 log h(x_i) = L   (9 eqs; unknowns x_1..x_9; L fixed),
# then verify the line z_i(s) = (1 + s x_i)/y_i, y_i = sign(F'(x_i)) sqrt(h(x_i)) at 50 digits: p1,p3,p5 = 0, p7 != 0,
# and the quintic weight form test (S34.1). usage: python3 glue.py <beta> <L> [seed]
import sys, numpy as np, mpmath as mp
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
beta = float(sys.argv[1]); L = float(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]) if len(sys.argv) > 3 else 0)

def V(x, hfun):
    d = x[:, None] - x[None, :]; np.fill_diagonal(d, 1)
    return np.log(np.abs(d)).sum(1) - 2.5*np.log(hfun(x))

def newton_real(x, F, J, iters=60):
    for _ in range(iters):
        r = F(x); dx = np.linalg.lstsq(J(x), r, rcond=None)[0]
        sc = min(1, 0.2*np.min(np.abs(x)+1e-3)/max(np.abs(dx).max(), 1e-300)); x = x - sc*dx
    return x, np.abs(F(x)).max()

# outer problem: 3 points, W_k = sum log|x_k-x_j| + log|x_k| - 2.5 log(x_k+1) = L
def Wout(x):
    d = x[:, None]-x[None, :]; np.fill_diagonal(d, 1)
    return np.log(np.abs(d)).sum(1) + np.log(np.abs(x)) - 2.5*np.log(x+1) - L
def Jout(x):
    d = x[:, None]-x[None, :]; np.fill_diagonal(d, 1); iD = 1/d; np.fill_diagonal(iD, 0)
    J = -iD; np.fill_diagonal(J, iD.sum(1) + 1/x - 2.5/(x+1)); return J
outs = []
for _ in range(3000):
    x0 = -1 + np.exp(rng.uniform(-4, 8, 3))
    try: x, r = newton_real(x0, Wout, Jout)
    except Exception: continue
    if np.isfinite(r) and r < 1e-11 and (x > -1).all() and np.min(np.abs(x)) > 1e-6:
        xs = np.sort(x)
        if np.min(np.diff(xs)) > 1e-8 and not any(np.allclose(xs, q) for q in outs): outs.append(xs)
print("outer solutions at L =", L, ":", [np.round(o, 5) for o in outs])

def full_check(xx, hfun):
    mp.mp.dps = 50
    x = [mp.mpf(v) for v in xx]
    Fp = [mp.fprod([x[i]-x[j] for j in range(9) if j != i]) for i in range(9)]
    y = [mp.sign(Fp[i])*mp.sqrt(hfun(x[i])) for i in range(9)]
    ratio = [Fp[i]**2/hfun(x[i])**5 for i in range(9)]
    Z = [1/yi for yi in y]; A = [xi/yi for xi, yi in zip(x, y)]
    out = {}
    for m in [1, 3, 5, 7]:
        # sum (Z + s A)^m = 0 for all s  <=>  sum Z^(m-k) A^k = 0 for all k
        out[m] = max(abs(mp.fsum([Z[i]**(m-k)*A[i]**k for i in range(9)])) for k in range(m+1))
    scale = max(abs(z) for z in Z)
    return out, scale, max(ratio)/min(ratio)

for xo in outs:
    for core in all_solutions(6, 1.0, 400, rng, rounds=1)[:1]:
        pass
    Lin = L - np.sum(np.log(np.abs(xo)))
    K = np.exp(2*Lin)
    print(f"outer {np.round(xo,4)}: core K = {K:.4g}", "(real core exists)" if 0 < K < 3.45 else "(no real core)")
    if not (0 < K < 3.45): continue
    cs = all_solutions(6, K, 600, rng, rounds=2)
    t = np.sort(cs[0].real)
    h = lambda x: (x+1)*(x*x+beta*beta)
    x0 = np.concatenate([beta*t, xo])
    Ff = lambda x: V(x, h) - L
    def Jf(x):
        d = x[:, None]-x[None, :]; np.fill_diagonal(d, 1); iD = 1/d; np.fill_diagonal(iD, 0)
        J = -iD; np.fill_diagonal(J, iD.sum(1) - 2.5*(1/(x+1) + 2*x/(x*x+beta*beta))); return J
    x, r = newton_real(x0, Ff, Jf, 80)
    print("   glued start residual", np.abs(Ff(x0)).max().round(4), "-> after Newton", r, " max rel move", np.max(np.abs(x-x0)/(np.abs(x0)+beta)).round(4))
    if r < 1e-10:
        hm = lambda v: (v+1)*(v*v+mp.mpf(beta)**2)
        # 50-digit polish by mp Newton
        mp.mp.dps = 50
        X = mp.matrix([mp.mpf(v) for v in x])
        for _ in range(8):
            R = mp.matrix(9, 1); J = mp.matrix(9, 9)
            for i in range(9):
                R[i] = mp.fsum([mp.log(abs(X[i]-X[j])) for j in range(9) if j != i]) - mp.mpf(2.5)*mp.log(hm(X[i])) - L
                for j in range(9):
                    if j != i: J[i, j] = -1/(X[i]-X[j])
                J[i, i] = mp.fsum([1/(X[i]-X[j]) for j in range(9) if j != i]) - mp.mpf(2.5)*(1/(X[i]+1) + 2*X[i]/(X[i]**2+mp.mpf(beta)**2))
            X = X - mp.lu_solve(J, R)
        res, sc, rr = full_check([X[i] for i in range(9)], hm)
        print("   x_i/beta (core):", np.round(np.array([float(v) for v in X[:6]])/beta, 4), " outer:", np.round(np.array([float(v) for v in X[6:]]), 4))
        print("   |sum Z^(m-k)A^k| max over k: p1 %.1e p3 %.1e p5 %.1e p7 %.3e  (|Z| scale %.2e); F'^2/h^5 max/min = %s" % (res[1], res[3], res[5], res[7], sc, mp.nstr(rr, 20)))
        # j-invariant of y^2 = (x+1)(x^2+beta^2)
        r_ = np.roots(np.poly([-1, 1j*beta, -1j*beta]))
        e1, e2, e3 = -1, 1j*beta, -1j*beta
        lam = (e3-e1)/(e2-e1); j = 256*(lam*lam-lam+1)**3/(lam*lam*(lam-1)**2)
        print("   j =", np.round(j.real, 2))
