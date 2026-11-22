"""Session 27: the P^3 Lambda spanned by an a-line and its first-order deformations. Is Lambda in L_135?"""
import numpy as np, sys
from sheets_tan import line_sys
np.set_printoptions(precision=4, suppress=True, linewidth=160)
def Lam(Z, a):
    K = np.linalg.svd(line_sys(Z, a)[1])[2][-5:]
    B = np.stack([Z, a], 1); Q = np.eye(9) - B @ np.linalg.pinv(B)
    W = np.hstack([np.stack([Q @ v[:9] for v in K], 1), np.stack([Q @ v[9:] for v in K], 1)])
    U, s, _ = np.linalg.svd(W); W = U[:, :2]
    M = np.hstack([B, W]); return np.linalg.qr(M)[0]
X = np.load(sys.argv[1])
rng = np.random.default_rng(0)
for x in X[:3]:
    L = Lam(x[:9], x[9:18])
    vals = []
    for _ in range(5):
        p = L @ rng.normal(size=4); p /= np.linalg.norm(p)
        vals.append([p.sum(), (p**3).sum(), (p**5).sum()])
    print(np.array(vals))
    print('Lambda basis (rows):'); print(L.T)
print('--- is b in Lambda?')
for x in X[:5]:
    L = Lam(x[:9], x[9:18]); b = x[18:]
    print(np.linalg.norm(b - L @ (L.T @ b)))
