# Minimise p4(y)/|y|^4 over points y on real lines {Q + k v} contained in V_3, for given r.
# Usage: python3 r5min.py <r> <starts> <seed>
import sys, numpy as np
from scipy.optimize import minimize
r = int(sys.argv[1]); N = int(sys.argv[2]); rng = np.random.default_rng(int(sys.argv[3]))
def zc(u):
    x = u[:r]; w = u[r::2] + 1j * u[r + 1::2]
    return np.concatenate([x.astype(complex), w, np.conj(w)])
def cons(X):
    Q, v = X[:9], X[9:]
    zQ, zv = zc(Q), zc(v)
    out = []
    for k in (1, 2, 3):
        for m in range(k + 1):
            out.append(np.sum(zQ ** (k - m) * zv ** m).real)
    out += [Q @ Q - 1, v @ v - 1, Q @ v]
    return np.array(out)
def obj(X):
    return np.sum(zc(X[:9]) ** 4).real   # p4 at Q; Q ranges over every point of the line
best = []
for i in range(N):
    X0 = rng.normal(size=18)
    res = minimize(obj, X0, constraints=[{'type': 'eq', 'fun': cons}], method='SLSQP', options={'maxiter': 500, 'ftol': 1e-12})
    if res.success and np.linalg.norm(cons(res.x)) < 1e-8:
        best.append(res.fun)
best = sorted(best)
print(f'r={r}: {len(best)} converged of {N}; smallest p4 values on real lines in V_3:', ['%.4f' % b for b in best[:6]], ' largest:', '%.4f' % best[-1] if best else None)

if len(sys.argv) > 4:
    np.set_printoptions(precision=6, suppress=True, linewidth=160)
    rng = np.random.default_rng(7)
    for i in range(40):
        res = minimize(obj, rng.normal(size=18), constraints=[{'type': 'eq', 'fun': cons}], method='SLSQP', options={'maxiter': 800, 'ftol': 1e-14})
        if res.success and np.linalg.norm(cons(res.x)) < 1e-9 and res.fun < 0.1202:
            Q, v = res.x[:9], res.x[9:]
            print('p4min = %.10f' % res.fun)
            print('zQ', zc(Q)); print('zv', zc(v))
            # look at the whole line: real parts and |w| along it
            for a in np.linspace(0, np.pi, 5)[:-1]:
                y = np.cos(a) * Q + np.sin(a) * v
                print('  a=%.2f x=' % a, np.round(np.sort(zc(y)[:r].real), 5), ' w=', np.round(zc(y)[r:r + (9 - r) // 2], 5), ' p4=%.5f' % np.sum(zc(y) ** 4).real)
            break
