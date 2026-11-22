#!/usr/bin/env python3
"""Session 53: real isotropic lines in V_12 = {p1 = p2 = 0} (K (x) R = R^r x C^s, n = 9)
and the real-root count of the binary quartic p4 on them.  Random isotropic 2-planes
of the trace form on {Tr = 0}.  usage: v12lines.py <r> <samples> <seed>"""
import sys, numpy as np
sys.path.insert(0, '.')
from c124real import coordmap
r, N, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(seed); M = coordmap(r); n = 9
G = (M.T @ M).real                      # trace form in real coordinates
t = (M.T @ np.ones(n)).real            # Tr(y) = t . x
# basis of {Tr = 0}
U = np.linalg.svd(t[None, :])[2][1:].T  # 9 x 8
Gt = U.T @ G @ U
ev, V = np.linalg.eigh(Gt)
neg = V[:, ev < 0] / np.sqrt(-ev[ev < 0]); pos = V[:, ev > 0] / np.sqrt(ev[ev > 0])
print('signature on Tr=0:', (ev > 0).sum(), (ev < 0).sum())
cnt = {}
for _ in range(N):
    O = np.linalg.qr(rng.standard_normal((pos.shape[1], pos.shape[1])))[0][:, :2]
    a = pos @ O; b = neg @ np.linalg.qr(rng.standard_normal((2, 2)))[0]
    L = U @ (a + b)                      # 9 x 2, isotropic
    th = np.linspace(0, np.pi, 4001)
    Y = (M @ (L[:, :1] * np.cos(th) + L[:, 1:] * np.sin(th)))
    p2 = np.sum(Y ** 2, 0).real; p4 = np.sum(Y ** 4, 0).real
    assert np.max(abs(p2)) < 1e-9
    ch = int(np.sum(np.sign(p4[1:]) != np.sign(p4[:-1])))
    cnt[ch] = cnt.get(ch, 0) + 1
print('sign changes of p4 on [0,pi):', dict(sorted(cnt.items())))
