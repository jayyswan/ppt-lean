# Session 35: all complex solutions of the bubble problem
#   F'(t_i)^2 = K * P(t_i)^5,  P = t^2 + 1,  F = prod (t - t_i), m roots, K fixed > 0
# (sig=-1 real forms are the solutions with t purely imaginary, by t -> i t.)
# Batched complex Newton on r_i = 2 sum_j log(t_i-t_j) - 5 log P(t_i) - log K  (mod 2 pi i).
# usage: python3 cbubble.py <m> <K list comma> <starts> [seed]   (prints counts and real / imaginary solutions)
import sys, numpy as np

def wrap(z):
    return z.real + 1j*((z.imag + np.pi) % (2*np.pi) - np.pi)

def newton(T, K, iters=100):
    S, m = T.shape
    I = np.eye(m, dtype=bool)
    lK = np.log(K+0j)
    for it in range(iters):
        D = T[:, :, None] - T[:, None, :]
        D[:, I] = 1.0
        P = T*T + 1
        R = wrap(2*np.log(D).sum(2) - 5*np.log(P) - lK)
        invD = 1.0/D; invD[:, I] = 0
        J = -2*invD
        J[:, I] = 2*invD.sum(2) - 10*T/P
        ok = np.isfinite(J).all((1, 2)) & np.isfinite(R).all(1)
        dT = np.zeros_like(T)
        if ok.any():
            try:
                dT[ok] = np.linalg.solve(J[ok], R[ok][:, :, None])[:, :, 0]
            except np.linalg.LinAlgError:
                pass
        lim = 0.25*(np.abs(T) + 0.05)
        sc = np.minimum(1.0, (lim/np.maximum(np.abs(dT), 1e-300)).min(1))
        T = T - sc[:, None]*dT
        bad = ~np.isfinite(T)
        T[bad] = 5.0 + 1j
    D = T[:, :, None] - T[:, None, :]; D[:, I] = 1.0
    R = wrap(2*np.log(D).sum(2) - 5*np.log(T*T + 1) - lK)
    return T, np.abs(R).max(1)

def canon(t):
    return np.array(sorted(t, key=lambda z: (round(z.real, 6), round(z.imag, 6))))

def all_solutions(m, K, starts, rng, rounds=6):
    sols = []
    for _ in range(rounds):
        T0 = (rng.normal(size=(starts, m)) + 1j*rng.normal(size=(starts, m))) * np.exp(rng.uniform(-1.5, 1.5, (starts, m)))
        T, res = newton(T0, K)
        for t, r in zip(T, res):
            if not (np.isfinite(r) and r < 1e-10): continue
            if np.abs(t).max() > 1e6: continue
            d = np.abs(t[:, None] - t[None, :]) + np.eye(m)
            if d.min() < 1e-6: continue
            if np.min(np.abs(t*t + 1)) < 1e-8: continue
            c = canon(t)
            if not any(np.allclose(c, q, atol=1e-7) for q in sols):
                sols.append(c)
    return sols

if __name__ == '__main__':
    m = int(sys.argv[1]); Ks = [float(x) for x in sys.argv[2].split(',')]
    starts = int(sys.argv[3]); seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    rng = np.random.default_rng(seed)
    for K in Ks:
        sols = all_solutions(m, K, starts, rng)
        real = [s for s in sols if np.abs(s.imag).max() < 1e-8]
        imag = [s for s in sols if np.abs(s.real).max() < 1e-8]
        print(f"m={m} K={K:g}: {len(sols)} complex solutions; real {len(real)}; purely imaginary {len(imag)}", flush=True)
        for s in real: print("   real ", np.array2string(np.sort(s.real), precision=4, max_line_width=200))
        for s in imag:
            v = np.sort(s.imag); print("   imag ", np.array2string(v, precision=4, max_line_width=200), " egg (v<-1):", int(np.sum(v < -1)), " |v|>1 all:", bool(np.all(np.abs(v) > 1)))
