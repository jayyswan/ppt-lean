# Session 35: fast batched Newton for the bubble problem
#   V_i = sum_{j!=i} log|t_i-t_j| - 2.5 log|t_i^2+sig| = L   (i = 1..m)
# usage: python3 bubble2.py <m> <sig> <Lmin> <Lmax> <nL> <starts> [seed]
# prints, per L, the distinct real solutions (sig=-1: only those with all |t_i|>1, and egg count k = #{t_i<-1}).
import sys, numpy as np

def newton_batch(T, sig, L, iters=80):
    S, m = T.shape
    I = np.eye(m, dtype=bool)
    for it in range(iters):
        D = T[:, :, None] - T[:, None, :]
        D[:, I] = 1.0
        R = np.log(np.abs(D)).sum(2) - 2.5*np.log(np.abs(T*T + sig)) - L
        invD = 1.0/D
        invD[:, I] = 0.0
        J = -invD.copy()
        diag = invD.sum(2) - 5*T/(T*T + sig)
        J[:, I] = diag
        try:
            dT = np.linalg.solve(J, R[:, :, None])[:, :, 0]
        except np.linalg.LinAlgError:
            dT = np.zeros_like(T)
            for s in range(S):
                try: dT[s] = np.linalg.lstsq(J[s], R[s], rcond=None)[0]
                except Exception: pass
        # damping: limit relative step
        lim = 0.3*(np.abs(T) + 0.1)
        sc = np.minimum(1.0, (lim/np.maximum(np.abs(dT), 1e-300)).min(1))
        T = T - sc[:, None]*dT
        T[~np.isfinite(T)] = 1e3
    D = T[:, :, None] - T[:, None, :]; D[:, I] = 1.0
    R = np.log(np.abs(D)).sum(2) - 2.5*np.log(np.abs(T*T + sig)) - L
    return T, np.abs(R).max(1)

def real_solutions(m, sig, L, starts, rng):
    if sig > 0:
        T0 = rng.choice([-1, 1], (starts, m)) * np.exp(rng.uniform(-3, 4, (starts, m)))
    else:
        T0 = rng.choice([-1, 1], (starts, m)) * (1 + np.exp(rng.uniform(-5, 4, (starts, m))))
    T, res = newton_batch(T0, sig, L)
    sols = []
    for t, r in zip(T, res):
        if not (np.isfinite(r) and r < 1e-11): continue
        ts = np.sort(t)
        if np.abs(ts).max() > 1e7: continue
        if np.min(np.diff(ts)) < 1e-7*(1+np.abs(ts).max()): continue
        if sig < 0 and np.min(np.abs(ts)) <= 1: continue
        if not any(np.allclose(ts, q, rtol=1e-7, atol=1e-9) for q in sols):
            sols.append(ts)
    return sols

if __name__ == '__main__':
    m = int(sys.argv[1]); sig = int(sys.argv[2])
    Ls = np.linspace(float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]))
    starts = int(sys.argv[6]); seed = int(sys.argv[7]) if len(sys.argv) > 7 else 0
    rng = np.random.default_rng(seed)
    for L in Ls:
        sols = real_solutions(m, sig, L, starts, rng)
        line = f"m={m} sig={sig:+d} L={L:+.2f}: {len(sols)}"
        if sig < 0:
            line += "  egg counts " + str(sorted(int(np.sum(s < -1)) for s in sols))
        print(line, flush=True)
        if '-v' in sys.argv:
            for s in sols: print("    ", np.array2string(s, precision=4, max_line_width=220))
