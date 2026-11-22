"""Session 27: structure of H^0(N) for the special lines (a-lines) of the pair family.
usage: python3 normal_type.py walk.npy"""
import numpy as np, sys
from sheets_tan import line_sys
np.set_printoptions(precision=4, suppress=True, linewidth=160)
def ker(Z, a, k):
    J = line_sys(Z, a)[1]
    return np.linalg.svd(J)[2][-k:]
def analyse(Z, a, k):
    K = ker(Z, a, k)
    B = np.stack([Z, a], 1); Q = np.eye(9) - B @ np.linalg.pinv(B)   # project mod span(Z,a)
    A0 = np.stack([Q @ v[:9] for v in K], 1); A1 = np.stack([Q @ v[9:] for v in K], 1)
    rk = lambda M: np.linalg.matrix_rank(M, 1e-7)
    vals = [rk(A0 + s * A1) for s in (0.3, -1.7, 2.9)]
    total = rk(np.hstack([A0, A1]))
    # dimension of sections of the form (value constant direction) etc: rank of [A0;A1] as map C^k -> C^18
    return vals, total, rk(np.vstack([A0, A1]))
X = np.load(sys.argv[1])
for x in X[:4]:
    Z, a, b = x[:9], x[9:18], x[18:]
    print('a-line (k=5):', analyse(Z, a, 5), ' b-line (k=3):', analyse(Z, b, 3))
