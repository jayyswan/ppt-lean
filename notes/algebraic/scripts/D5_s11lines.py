"""Count distinct complex good lines in X cap H (split model, n = 9).
X = {sum y = sum y^3 = sum y^5 = 0} in P^8; H a random rational hyperplane of the trace-zero space.
Line spanned by u = w1 + sum_k a_k w_k, v = w2 + sum_k b_k w_k (k = 3..7), w a basis of W = H cap {sum = 0}.
Equations: coefficients of s^j in sum (u+sv)^3 (4) and sum (u+sv)^5 (6). Newton from random complex starts.
Usage: py -I s11lines.py SEED NSTARTS
"""
import sys
import numpy as np
from math import comb

seed, nst = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)
hr = np.random.default_rng(11)
# trace-zero basis e_i - e_9, i = 1..8
tb = np.zeros((8, 9))
for i in range(8):
    tb[i, i], tb[i, 8] = 1, -1
h = hr.integers(-5, 6, 8).astype(float)          # hyperplane sum h_i c_i = 0 in tb-coordinates
# basis of {c : h.c = 0} (7-dim), via SVD, then to y-space
_, _, vt = np.linalg.svd(h[None, :])
Wc = vt[1:]                                        # 7 x 8
W = Wc @ tb                                        # 7 x 9 rows in y-space


def eqs(z):
    a, b = z[:5], z[5:]
    u = W[0] + a @ W[2:]
    v = W[1] + b @ W[2:]
    out = []
    for d in (3, 5):
        for j in range(d + 1):
            out.append(comb(d, j) * np.sum(u ** (d - j) * v ** j))
    return np.array(out)


def jac(z):
    a, b = z[:5], z[5:]
    u = W[0] + a @ W[2:]
    v = W[1] + b @ W[2:]
    J = np.zeros((10, 10), complex)
    r = 0
    for d in (3, 5):
        for j in range(d + 1):
            c = comb(d, j)
            du = (d - j) * u ** max(d - j - 1, 0) * v ** j if d - j > 0 else np.zeros(9)
            dv = j * u ** (d - j) * v ** max(j - 1, 0) if j > 0 else np.zeros(9)
            J[r, :5] = c * (W[2:] @ du)
            J[r, 5:] = c * (W[2:] @ dv)
            r += 1
    return J


def newton(z):
    for it in range(80):
        f = eqs(z)
        nf = np.linalg.norm(f)
        if nf < 1e-13:
            return z, nf
        try:
            dz = np.linalg.solve(jac(z), -f)
        except np.linalg.LinAlgError:
            return None, None
        lam = 1.0
        while lam > 1e-4:
            zn = z + lam * dz
            if np.linalg.norm(eqs(zn)) < nf:
                break
            lam /= 2
        z = zn
        if np.linalg.norm(z) > 1e6:
            return None, None
    return (z, np.linalg.norm(eqs(z))) if np.linalg.norm(eqs(z)) < 1e-11 else (None, None)


def oddsums(z):
    a, b = z[:5], z[5:]
    u = W[0] + a @ W[2:]
    v = W[1] + b @ W[2:]
    m = max(np.abs(u).max(), np.abs(v).max())
    u, v = u / m, v / m
    return max(abs(np.sum((u + s * v) ** 7)) for s in (0.3, -0.7 + 0.2j, 1.1j))


sols = []
for k in range(nst):
    z0 = (rng.normal(size=10) + 1j * rng.normal(size=10)) * rng.choice([0.3, 1, 3])
    z, r = newton(z0)
    if z is None:
        continue
    if abs(np.linalg.det(jac(z))) < 1e-8 * max(1, np.linalg.norm(z)) ** 10:
        continue  # singular: not a reduced isolated point (pairing contacts land here)
    if oddsums(z) < 1e-6:
        continue  # pairing line (all odd power sums vanish)
    if all(np.linalg.norm(z - w) > 1e-6 * (1 + np.linalg.norm(z)) for w in sols):
        sols.append(z)
nreal = sum(1 for z in sols if np.abs(z.imag).max() < 1e-8)
print(f"seed {seed} starts {nst}: distinct nonsingular good lines {len(sols)}, real {nreal}")
np.save(f"s11_seed{seed}.npy", np.array(sols))
