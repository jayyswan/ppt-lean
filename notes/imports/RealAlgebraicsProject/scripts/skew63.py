# Session 63 (S63.2): extremal values of I = -(8/45) gamma^2 on real L_135^(10)
# (10 real points, p1 = p3 = p5 = 0). gamma = skewness of V_i = y_i^2.
# Usage: python3 skew63.py <starts> <seed>
import sys, numpy as np
from scipy.optimize import minimize
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 1)

def gam2(y):
    V = y**2; m = V.mean(); s2 = ((V-m)**2).mean(); mu3 = ((V-m)**3).mean()
    return mu3**2/s2**3
cons = [{'type': 'eq', 'fun': (lambda y, k=k: np.sum(y**k))} for k in (1, 3, 5)]
cons.append({'type': 'eq', 'fun': lambda y: np.sum(y**2) - 10.0})
best = []
for it in range(N):
    y0 = rng.normal(size=10)
    for sgn in (1,):
        r = minimize(lambda y: -gam2(y), y0, constraints=cons, method='SLSQP',
                     options={'maxiter': 2000, 'ftol': 1e-14})
        if not r.success: continue
        y = r.x
        res = max(abs(np.sum(y**k)) for k in (1, 3, 5))
        if res > 1e-8: continue
        V = np.sort(y**2)
        # structure: distinct |y| values and minimal coordinate separation, pairing count
        ys = np.sort(y)
        sep = np.min(np.diff(ys))
        pairs = sum(1 for i in range(10) for j in range(i+1, 10) if abs(y[i]+y[j]) < 1e-5)
        best.append((gam2(y), sep, pairs, np.round(V, 5), np.round(ys, 4)))
best.sort(key=lambda t: -t[0])
print('converged', len(best), 'of', N)
print('max gamma^2 =', best[0][0], '(9/4 =', 9/4, ')  I_min =', -8/45*best[0][0])
for b in best[:6]:
    print('g2=%.9f sep=%.2e pairs=%d' % b[:3], 'y=', b[4])
# local maxima with non-degenerate structure (sep > 1e-3 and no pairs)
nd = [b for b in best if b[1] > 1e-3 and b[2] == 0]
print('nondegenerate local maxima:', len(nd))
for b in nd[:6]:
    print('  g2=%.9f sep=%.2e' % (b[0], b[1]), 'y=', b[4])
hist = np.histogram([b[0] for b in best], bins=[0, .5, 1, 1.5, 2, 2.2, 2.24, 2.249, 2.2501])[0]
print('histogram of local maxima of gamma^2:', hist)
