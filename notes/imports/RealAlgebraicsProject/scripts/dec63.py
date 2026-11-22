# Session 63 (S63.6): real points of {p1 = p3 = p5 = 0} in R^r x C^s (n = r + 2s) with distinct
# coordinates and full-rank Jacobian: the real test for the decic row (n = 10: a Q-quintic graph
# with the Bezier (t^2, cubic) crosses exactly at the 10 conjugates; no auxiliary crossing).
# Usage: python3 dec63.py <n> <N starts> <seed>
import sys, numpy as np
n = int(sys.argv[1]); N = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
for r in range(n % 2, n+1, 2):
    s = (n - r)//2
    good = 0
    for it in range(N):
        x = rng.normal(size=r + 2*s)
        def coords(x):
            re = x[:r]; c = x[r:r+s] + 1j*x[r+s:]
            return np.concatenate([re, c, np.conj(c)])
        for _ in range(200):
            y = coords(x)
            F = np.array([np.real(np.sum(y**k)) for k in (1, 3, 5)])
            # real Jacobian wrt x
            J = np.zeros((3, r+2*s))
            for a, k in enumerate((1, 3, 5)):
                d = k*y**(k-1)
                J[a, :r] = np.real(d[:r])
                J[a, r:r+s] = 2*np.real(d[r:r+s])
                J[a, r+s:] = -2*np.imag(d[r:r+s])
            dx = np.linalg.lstsq(J, -F, rcond=None)[0]
            x = x + dx
            if np.linalg.norm(F) < 1e-13: break
        y = coords(x)
        F = np.array([abs(np.sum(y**k)) for k in (1, 3, 5)])
        sep = min(abs(y[i]-y[j]) for i in range(n) for j in range(i+1, n))
        pair = min(abs(y[i]+y[j]) for i in range(n) for j in range(i+1, n))
        if F.max() < 1e-10 and sep > 1e-3 and pair > 1e-3 and np.linalg.matrix_rank(J, 1e-8) == 3 and (s == 0 or np.min(np.abs(np.imag(y[r:r+s]))) > 1e-3):
            good += 1
    print('n=%d r=%d s=%d: %d of %d starts give smooth real points with distinct, unpaired coordinates' % (n, r, s, good, N))
