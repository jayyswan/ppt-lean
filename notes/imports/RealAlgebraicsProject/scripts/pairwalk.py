"""Session 27: walk along the 1-dim family of meeting pairs by perturb-and-resolve;
at each sample report the line-system kernel dimension (S tangent dim + 1 gauge) for each line.
usage: python3 pairwalk.py pairs_1.npy steps stepsize -> walk.npy"""
import numpy as np, sys
from lp_core import solve, degenerate
from sheets_tan import line_sys
X = np.load(sys.argv[1]); steps = int(sys.argv[2]); h = float(sys.argv[3])
rng = np.random.default_rng(5)
def kdim(Z, a):
    s = np.linalg.svd(line_sys(Z, a)[1], compute_uv=False)
    return 18 - (s > 1e-6 * s[0]).sum(), s[-3]
x = X[0]; out = [x]; prev = x
for k in range(steps):
    # step roughly along the curve: extrapolate from previous displacement if any
    d = x - prev if k > 0 else rng.normal(size=27) * h
    if np.linalg.norm(d) > 0: d = d / np.linalg.norm(d) * h
    y, r, J = solve(x + d + rng.normal(size=27) * h * 0.1)
    if r > 1e-11 or degenerate(y[:9], y[9:18], y[18:]):
        print('lost', r); h /= 2; continue
    # fix line labelling (a with a, b with b) by sign/proximity
    for sl in (slice(9, 18), slice(18, 27)):
        if np.linalg.norm(y[sl] + x[sl]) < np.linalg.norm(y[sl] - x[sl]): y[sl] = -y[sl]
    if np.linalg.norm(y[:9] + x[:9]) < np.linalg.norm(y[:9] - x[:9]): y = -y
    prev, x = x, y; out.append(x)
    ka, sa = kdim(x[:9], x[9:18]); kb, sb = kdim(x[:9], x[18:])
    print(k, 'dist', round(np.linalg.norm(x - prev), 4), 'kernel a', ka, 'kernel b', kb, flush=True)
np.save('walk.npy', np.array(out))
