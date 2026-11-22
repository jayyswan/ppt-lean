# Real lines in V' = {p1 = p2 = p4 = 0} (all polarizations along the line), by least squares.
# Usage: python3 vprime.py <r> <starts> <seed>
import sys, numpy as np
from scipy.optimize import least_squares
r = int(sys.argv[1]); N = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
def zc(u):
    x = u[:r]; w = u[r::2] + 1j * u[r + 1::2]
    return np.concatenate([x.astype(complex), w, np.conj(w)])
def F(X):
    Q, v = X[:9], X[9:]; zQ, zv = zc(Q), zc(v)
    out = [np.sum(zQ ** (k - m) * zv ** m).real for k in (1, 2, 4) for m in range(k + 1)]
    return np.array(out + [Q @ Q - 1, v @ v - 1, Q @ v])
ok = 0; p3real = []
for i in range(N):
    res = least_squares(F, rng.normal(size=18), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=4000)
    if np.linalg.norm(F(res.x)) < 1e-10:
        Q, v = res.x[:9], res.x[9:]; z = zc(Q)
        if min(abs(z[a] - z[b]) for a in range(9) for b in range(a)) < 1e-4: continue
        ok += 1
print(f'r={r}: genuine real lines in V\' found in {ok} of {N} starts')
