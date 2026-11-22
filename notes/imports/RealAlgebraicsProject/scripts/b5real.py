# Session 62: real test for row B5 on L135 (zeta = 0 slice, n = 9) and on L135^(10) (padded, n = 10).
# Usage: python3 b5real.py <r> <n> <N> <seed>
# Samples real points of {p1 = p3 = p5 = 0} in R^r x C^s (n = r + 2s coordinates; for n = 10 the
# last real coordinate is the auxiliary crossing zeta), prints the range of
#   b2 = (p2^3 - 15 p2 p4 + 50 p6)/p2^3  (B2 = 0 <=> I = 0, the odd-quintic class)
#   b3 = (p2^2 - 10 p4)/p2^2             (B3 = 0 <=> pure x^5 + x^2 class)
# and the class invariant I = B2^2/B3^3 (normalised), plus sign changes of b2.
import sys, numpy as np
r, n, N, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
s = (n - r)//2
rng = np.random.default_rng(seed)
def coords(x):
    re = x[:r]; c = x[r:r+s] + 1j*x[r+s:]
    return np.concatenate([re, c, np.conj(c)])
def P(x, k): return np.real(np.sum(coords(x)**k))
def F(x): return np.array([P(x, 1), P(x, 3), P(x, 5)])
def J(x, h=1e-7):
    f0 = F(x); M = np.zeros((3, n))
    for i in range(n):
        d = np.zeros(n); d[i] = h; M[:, i] = (F(x + d) - f0)/h
    return M
B2s, B3s, Is = [], [], []
fails = 0
for t in range(N):
    x = rng.normal(size=n)
    ok = False
    for it in range(80):
        f = F(x)
        if np.abs(f).max() < 1e-13*max(1, np.abs(x).max()**5): ok = True; break
        x = x - np.linalg.pinv(J(x)) @ f
    if not ok or not np.all(np.isfinite(x)): fails += 1; continue
    z = coords(x)
    if n == 9 or True:
        sep = min(abs(z[i]-z[j]) for i in range(n) for j in range(i+1, n))
        if sep < 1e-6: fails += 1; continue
    p2, p4, p6 = P(x, 2), P(x, 4), P(x, 6)
    b2 = (p2**3 - 15*p2*p4 + 50*p6)/p2**3
    b3 = (p2**2 - 10*p4)/p2**2
    B2s.append(b2); B3s.append(b3)
    # I = B2^2/B3^3 with B2 = -p2^3 b2/300, B3 = p2^2 b3/40
    Is.append(((b2/300)**2)/((b3/40)**3))
B2s, B3s, Is = map(np.array, (B2s, B3s, Is))
print(f'r={r} n={n}: {len(B2s)} real points ({fails} failed)')
print('b2 range [%.4f, %.4f], fraction b2>0: %.3f' % (B2s.min(), B2s.max(), np.mean(B2s > 0)))
print('b3 range [%.4f, %.4f]' % (B3s.min(), B3s.max()))
q = np.quantile(Is, [0, .05, .25, .5, .75, .95, 1])
print('I quantiles', np.round(q, 4))
