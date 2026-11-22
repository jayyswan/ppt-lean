"""Session 27: tangent spaces of the two sheets of V (3-fold swept by lines of S) at a meeting point.
usage: python3 sheets_tan.py pairs_1.npy"""
import numpy as np, sys
from lp_core import line_eqs, FJ
n = 9
def line_sys(Z, a):
    o, J = line_eqs(Z, a, True)
    F = np.array(o + [Z @ Z - 1, Z @ a, a @ a - 1])
    rows = [np.concatenate([dZ, da]) for dZ, da in J]
    rows += [np.concatenate([2 * Z, 0 * Z]), np.concatenate([a, Z]), np.concatenate([0 * Z, 2 * a])]
    return F, np.array(rows)
def tanL(Z):
    # tangent space of L_135 at Z (linear, in C^9): kernel of gradients of p1,p3,p5
    G = np.stack([np.ones(n), 3 * Z**2, 5 * Z**4])
    return np.linalg.svd(G)[2][3:].T   # 9 x 6
def sheet(Z, a):
    F, J = line_sys(Z, a)
    sv = np.linalg.svd(J, compute_uv=False)
    K = np.linalg.svd(J)[2][-3:]       # kernel (3: 2 for S + 1 gauge)
    vecs = [Z, a] + [k[:9] for k in K]
    U, s, _ = np.linalg.svd(np.stack(vecs, 1), full_matrices=False)
    r = (s > 1e-8 * s[0]).sum()
    return U[:, :r], sv[-4:]
def inter_dim(A, B):
    s = np.linalg.svd(np.hstack([A, B]), compute_uv=False)
    r = (s > 1e-8 * s[0]).sum()
    return A.shape[1] + B.shape[1] - r
if __name__ == '__main__':
  X = np.load(sys.argv[1])
  for x in X:
      Z, a, b = x[:9], x[9:18], x[18:]
      T1, sv1 = sheet(Z, a); T2, sv2 = sheet(Z, b); TL = tanL(Z)
      F, J = FJ(x)
      print('res', np.linalg.norm(F), 'pair sv', np.round(np.linalg.svd(J, compute_uv=False)[-4:], 8))
      print('  line sv', sv1, sv2)
      print('  dim T1, T2 =', T1.shape[1], T2.shape[1], ' dim T1∩T2 =', inter_dim(T1, T2),
            ' T1 in TL:', inter_dim(T1, TL), ' T2 in TL:', inter_dim(T2, TL))
      # principal angles between T1 and T2
      s = np.linalg.svd(T1.T @ T2, compute_uv=False)
      print('  cos principal angles', np.round(s, 6))
