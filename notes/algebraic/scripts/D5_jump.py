"""D5: first-order jump locus of the zero scheme Z on a pairing component G(2, Lambda_pi).
Lambda_pi: y = (a, -a, b, -b, c, -c, d, -d, 0). Line l = span(A, B), alpha_i(t) = A_i + t B_i.
Normal map (B3 2a): s_i(t) = s_i0 + s_i1 t (i = 1..4) |-> (sum alpha_i^2 s_i, sum alpha_i^4 s_i),
coefficients in t: 4 + 6 = 10 equations on 8 unknowns. Z = Y near l iff this has rank 8.
Usage: py -I D5_jump.py SEED NSTARTS
"""
import sys
import numpy as np
from numpy.polynomial import polynomial as P

seed, nst = int(sys.argv[1]), int(sys.argv[2])
rng = np.random.default_rng(seed)


def Mmat(A, B):
    al = [np.array([A[i], B[i]]) for i in range(4)]
    rows3, rows5 = np.zeros((4, 8), complex), np.zeros((6, 8), complex)
    for i in range(4):
        a2 = P.polypow(al[i], 2)
        a4 = P.polypow(al[i], 4)
        for k in range(2):           # s_i = t^k
            sh = np.zeros(2, complex); sh[k] = 1
            c3 = P.polymul(a2, sh); c5 = P.polymul(a4, sh)
            rows3[:len(c3), 2 * i + k] = c3
            rows5[:len(c5), 2 * i + k] = c5
    return np.vstack([rows3, rows5])


# 1. generic rank, and the singular-value profile at random lines
sv = [np.linalg.svd(Mmat(*(rng.normal(size=(2, 4)) + 1j * rng.normal(size=(2, 4)))), compute_uv=False) for _ in range(200)]
print("generic: min over 200 lines of sigma_8/sigma_1 =", min(s[-1] / s[0] for s in sv))

# 2. rank-drop locus: unknowns (a2,a3,b2,b3) chart A=(1,0,a2,a3), B=(0,1,b2,b3), kernel s (8), with
#    M s = 0 (10), r.s = 1 (1), and k random linear slices on (a,b). Report the dimension by trying k = 0..3.
def F(z, r, Ls):
    a2, a3, b2, b3 = z[:4]
    s = z[4:]
    A = np.array([1, 0, a2, a3]); B = np.array([0, 1, b2, b3])
    out = list(Mmat(A, B) @ s) + [r @ s - 1]
    for L, c in Ls:
        out.append(L @ z[:4] - c)
    return np.array(out)


def numjac(f, z, h=1e-7):
    f0 = f(z)
    J = np.zeros((len(f0), len(z)), complex)
    for k in range(len(z)):
        e = np.zeros(len(z), complex); e[k] = h
        J[:, k] = (f(z + e) - f0) / h
    return J


def solve(f, z):
    for _ in range(100):
        fz = f(z)
        if np.linalg.norm(fz) < 1e-12:
            return z
        J = numjac(f, z)
        dz = np.linalg.lstsq(J, -fz, rcond=None)[0]
        z = z + dz
        if np.linalg.norm(z) > 1e5:
            return None
    return z if np.linalg.norm(f(z)) < 1e-10 else None


r = rng.normal(size=8) + 1j * rng.normal(size=8)
for k in range(0, 4):
    Ls = [(rng.normal(size=4) + 1j * rng.normal(size=4), rng.normal() + 1j * rng.normal()) for _ in range(k)]
    f = lambda z: F(z, r, Ls)
    found = []
    for _ in range(nst):
        z = solve(f, rng.normal(size=12) + 1j * rng.normal(size=12))
        if z is not None:
            found.append(z)
    # local dimension at found points: 12 - rank of Jacobian of the 11 + k equations
    dims = sorted(set(12 - np.linalg.matrix_rank(numjac(f, z), tol=1e-5) for z in found))
    print(f"slices {k}: solutions {len(found)}, local solution-set dimensions {dims}")
    if found:
        z = found[0]
        A = np.array([1, 0, *z[:2]]); B = np.array([0, 1, *z[2:4]])
        print("   sample line A, B:", np.round(A, 4), np.round(B, 4))
        # is it on a pairwise intersection (alpha_i = 0 or alpha_i = +-alpha_j identically)?
        al = [np.array([A[i], B[i]]) for i in range(4)]
        deg = min([np.linalg.norm(x) for x in al] +
                  [min(np.linalg.norm(al[i] - al[j]), np.linalg.norm(al[i] + al[j])) for i in range(4) for j in range(i)])
        print("   distance to pairwise-intersection lines:", deg)
