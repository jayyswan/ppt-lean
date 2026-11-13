import sys, numpy as np
exec(open('D5_jump.py').read().split('# 1. generic rank')[0].replace('seed, nst = int(sys.argv[1]), int(sys.argv[2])', 'seed, nst = 7, 0'))
src = open('D5_jump.py').read()
exec(src[src.index('def F('):src.index('r = rng.normal')])
rng = np.random.default_rng(int(sys.argv[1])); nst = int(sys.argv[2])
r = rng.normal(size=8) + 1j * rng.normal(size=8)
from collections import Counter
cnt = Counter()
for k in (0, 1, 2):
    Ls = [(rng.normal(size=4) + 1j * rng.normal(size=4), rng.normal() + 1j * rng.normal()) for _ in range(k)]
    f = lambda z: F(z, r, Ls)
    for _ in range(nst):
        z = solve(f, rng.normal(size=12) + 1j * rng.normal(size=12))
        if z is None: continue
        A = np.array([1, 0, *z[:2]]); B = np.array([0, 1, *z[2:4]])
        al = [np.array([A[i], B[i]]) for i in range(4)]
        kd = 8 - np.linalg.matrix_rank(Mmat(A, B), tol=1e-7)
        tot = 12 - np.linalg.matrix_rank(numjac(f, z), tol=1e-5) + k
        linedim = tot - (kd - 1)
        pat = []
        for i in range(4):
            if np.linalg.norm(al[i]) < 1e-6: pat.append(f"a{i}=0")
        for i in range(4):
            for j in range(i):
                if abs(al[i][0] * al[j][1] - al[i][1] * al[j][0]) < 1e-6 and np.linalg.norm(al[j]) > 1e-6 and np.linalg.norm(al[i]) > 1e-6:
                    lam = (al[i] @ al[j].conj()) / (al[j] @ al[j].conj())
                    tag = "+-1" if min(abs(lam - 1), abs(lam + 1)) < 1e-6 else ("+-i" if min(abs(lam - 1j), abs(lam + 1j)) < 1e-6 else "other")
                    pat.append(f"a{i}~a{j}({tag})")
        cnt[(linedim, kd, tuple(sorted(pat)))] += 1
for key, v in sorted(cnt.items(), key=lambda kv: -kv[1]):
    print(v, "line-locus dim", key[0], "kernel dim", key[1], "pattern", key[2])
