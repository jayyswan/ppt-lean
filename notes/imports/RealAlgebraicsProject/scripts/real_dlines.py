# Real lines on D for each signature r: real model of K (x) R = R^r x C^s, conjugates (x_1..x_r, w_1, conj w_1, ...).
# A P-rational line on D_K must be real in this model. Least squares from random starts; report how many converge.
import numpy as np, sys
from scipy.optimize import least_squares
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
def model(r):
    s = (9 - r)//2
    def conj(v):
        z = list(v[:r] + 0j)
        for k in range(s):
            w = v[r+2*k] + 1j*v[r+2*k+1]; z += [w, np.conj(w)]
        return np.array(z)
    return conj
def P(z, k): return np.sum(z**k).real
Q4 = lambda z: 6*P(z,4) - P(z,2)**2
Q5 = lambda z: 18*P(z,5) - 5*P(z,2)*P(z,3)
def run(r, trials=int(sys.argv[3]) if len(sys.argv) > 3 else 60):
    conj = model(r)
    # trace-zero: Tr = sum of real coords + 2 * sum of Re parts; solve for first coordinate
    w = np.array([1.0]*r + [2.0, 0.0]*((9-r)//2))
    def vec(u): return np.concatenate([[-(w[1:] @ u)/w[0]], u])
    ts = [0, 1, -1, 2, -2, 0.5]
    def resid(x):
        a, b = vec(x[:8]), vec(x[8:])
        out = [Q4(conj(a + t*b)) for t in ts[:5]] + [Q4(conj(b))] + [Q5(conj(a + t*b)) for t in ts] + [Q5(conj(b))]
        return np.array(out + [x[:8]@x[:8] - 1, x[8:]@x[8:] - 1, x[:8]@x[8:]])
    found, nondeg = 0, 0
    for t in range(trials):
        sol = least_squares(resid, rng.normal(size=16), xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=1500)
        if np.max(np.abs(sol.fun)) > 1e-10: continue
        found += 1
        a, b = conj(vec(sol.x[:8])), conj(vec(sol.x[8:]))
        if not any(abs(a[i]-a[j]) + abs(b[i]-b[j]) < 1e-6 for i in range(9) for j in range(i+1, 9)): nondeg += 1
    return found, nondeg
for r in [int(c) for c in sys.argv[2].split(",")]:
    print('r =', r, ': real lines on D found / with distinct conjugates =', run(r))
