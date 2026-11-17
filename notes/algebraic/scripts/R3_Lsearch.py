"""Search V_tau over a real quadratic field L = Q(sqrt d).

Conventions: K = Q[b]/q.  K_L = K + sqrt(d) K, represented as pairs (A,B).
tau = tau0 + sqrt(d) tau1.  W_tau = L-span{1,tau,tau^2} (6-dimensional over Q).
rho = (A,B); rho^2 = (A^2 + d B^2, 2 A B).
We enumerate rho with all 14 rational coordinates in [-H,H], keep rho^2 in W_tau,
and read off Q(s) = c s^2 + b s + a with a,b,c in L.

Usage: py -3 R3_Lsearch.py n7 5 "beta,b2" H
       tau spec is a comma list of coefficient vectors, e.g. "beta,b2" = beta + sqrt(d) beta^2.
"""

import sys
from fractions import Fraction

import numpy as np

from R3_search import NF, Q7, Q6, Q5, kernel, mat_rank

QS = {"n5": Q5, "n6": Q6, "n7": Q7}


def tau_from_spec(F, spec):
    """spec: 'beta', 'b2', 'bp1', ...; returns (tau0, tau1) coefficient lists."""
    def one(s):
        v = [0] * F.n
        if s == "1":
            v[0] = 1
        elif s == "beta":
            v[1] = 1
        elif s == "b2":
            v[2] = 1
        elif s == "bp1":
            v[0] = 1
            v[1] = 1
        elif s == "b2p1":
            v[0] = 1
            v[2] = 1
        else:
            raise SystemExit(f"unknown tau atom {s}")
        return v

    parts = spec.split("+")
    tau0 = [0] * F.n
    tau1 = [0] * F.n
    for part in parts:
        # atoms before the last go into tau0; a trailing atom is the sqrt(d) part
        pass
    # syntax: "u;v" where u is the rational part and v the sqrt(d) part
    if ";" in spec:
        u, v = spec.split(";")
        for s in u.split("+") if u else []:
            tau0 = [x + y for x, y in zip(tau0, one(s))]
        for s in v.split("+") if v else []:
            tau1 = [x + y for x, y in zip(tau1, one(s))]
    else:
        for s in parts:
            tau0 = [x + y for x, y in zip(tau0, one(s))]
    return tau0, tau1


def mul(F, a, b):
    return [int(x) for x in F.mul(a, b)]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(a, t):
    return [t * x for x in a]


class KL:
    def __init__(self, F, d):
        self.F = F
        self.d = d
        self.n = F.n

    def mul(self, x, y):
        A, B = x
        C, D = y
        AC = mul(self.F, A, C)
        BD = mul(self.F, B, D)
        AD = mul(self.F, A, D)
        BC = mul(self.F, B, C)
        return (add(AC, scale(BD, self.d)), add(AD, BC))

    def sq(self, x):
        return self.mul(x, x)


def complement(W, dim):
    rows = [[Fraction(x) for x in w] for w in W]
    bas = kernel(rows, dim)
    out = []
    for v in bas:
        den = 1
        for z in v:
            den = den * z.denominator // _gcd(den, z.denominator)
        out.append([int(z * den) for z in v])
    return out


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


def quad_matrix(F, r):
    """Symmetric matrix of the quadratic form x -> r . x^2 on K (7x7)."""
    n = F.n
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            s = 0
            for k in range(n):
                s += r[k] * F.mult[k][i][j]
            M[i][j] = s
    return M


def build_forms(F, d, tau0, tau1):
    """Return 8 quadratic matrices on Q^14 vanishing on W_tau."""
    n = F.n
    one = ([1] + [0] * (n - 1), [0] * n)
    tau = (tau0, tau1)
    tau2 = (add(mul(F, tau0, tau0), scale(mul(F, tau1, tau1), d)),
            scale(mul(F, tau0, tau1), 2))
    # L-basis of W: w, sqrt(d) w for w = 1, tau, tau2
    W = []
    for (U, V) in (one, tau, tau2):
        W.append(U + V)
        W.append(scale(V, d) + U)  # sqrt(d)*(U + sqrt(d)V) = dV + U sqrt(d)
    W = [[int(x) for x in w] for w in W]
    comp = complement(W, 2 * n)
    mats = []
    for r in comp:
        rU, rV = r[:n], r[n:]
        MU = quad_matrix(F, rU)
        MV = quad_matrix(F, rV)
        M = [[0] * (2 * n) for _ in range(2 * n)]
        for i in range(n):
            for j in range(n):
                M[i][j] = MU[i][j]
                M[i + n][j + n] = d * MU[i][j]
                M[i][j + n] = MV[i][j]
                M[i + n][j] = MV[i][j]
        mats.append(M)
    return W, comp, mats


def pos_L(u0, u1, d):
    """Exact test u0 + u1*sqrt(d) > 0 for d > 0 squarefree."""
    if u1 == 0:
        return u0 > 0
    if u1 > 0:
        if u0 >= 0:
            return True
        return u0 * u0 < d * u1 * u1
    if u0 <= 0:
        return False
    return u0 * u0 > d * u1 * u1


def solve_coeffs(W, rhs):
    """Solve rhs = a0*w0 + ... in Q^6; return (a0..a5) or None."""
    m = [[Fraction(W[j][i]) for j in range(6)] for i in range(len(rhs))]
    r = [Fraction(x) for x in rhs]
    nr = len(r)
    row = 0
    piv = []
    for col in range(6):
        p = None
        for i in range(row, nr):
            if m[i][col] != 0:
                p = i
                break
        if p is None:
            continue
        m[row], m[p] = m[p], m[row]
        r[row], r[p] = r[p], r[row]
        pv = m[row][col]
        m[row] = [x / pv for x in m[row]]
        r[row] /= pv
        for i in range(nr):
            if i != row and m[i][col] != 0:
                f = m[i][col]
                m[i] = [m[i][k] - f * m[row][k] for k in range(6)]
                r[i] -= f * r[row]
        piv.append(col)
        row += 1
    for i in range(row, nr):
        if r[i] != 0:
            return None
    sol = [Fraction(0)] * 6
    for i, col in enumerate(piv):
        sol[col] = r[i]
    return sol


def run(mode, d, spec, H):
    F = NF([int(x) for x in QS[mode]])
    n = F.n
    tau0, tau1 = tau_from_spec(F, spec)
    W, comp, mats = build_forms(F, d, tau0, tau1)
    print(f"{mode} L=Q(sqrt {d}) tau={spec} H={H}: W rank {mat_rank(W)}, complement {len(comp)}")
    found = []
    grid = np.arange(-H, H + 1, dtype=np.int64)
    # chunk over the first 5 coordinates, enumerate the remaining 2n-5
    free = 2 * n - 5
    rest = np.stack(np.meshgrid(*([grid] * free), indexing="ij"), axis=-1).reshape(-1, free)
    for head in np.ndindex(*([2 * H + 1] * 5)):
        V = np.empty((rest.shape[0], 2 * n), dtype=np.int64)
        V[:, :5] = head
        V[:, 5:] = rest
        ok = np.ones(V.shape[0], dtype=bool)
        for M in mats:
            M = np.asarray(M, dtype=np.int64)
            vals = np.einsum("ij,jk,ik->i", V, M, V)
            ok &= vals == 0
        for row in V[ok]:
            rho = (list(map(int, row[:n])), list(map(int, row[n:])))
            rho2 = (add(mul(F, rho[0], rho[0]), scale(mul(F, rho[1], rho[1]), d)),
                    scale(mul(F, rho[0], rho[1]), 2))
            sol = solve_coeffs(W, rho2[0] + rho2[1])
            if sol is None:
                continue
            a0, a1, b0, b1, c0, c1 = sol
            # Q(s) = (c0 + sqrt(d) c1) s^2 + (b0 + sqrt(d) b1) s + (a0 + sqrt(d) a1)
            found.append(((a0, a1), (b0, b1), (c0, c1), tuple(rho[0]), tuple(rho[1])))
    print(f"  solutions: {len(found)}")
    pd = []
    nondeg = []
    for (a0, a1), (b0, b1), (c0, c1), A, B in found:
        # exact L-arithmetic: disc = 4ac - b^2 = (D0, D1)
        if c0 == 0 and c1 == 0:
            continue  # linear, not a binary quadratic form
        D0 = 4 * (a0 * c0 + d * a1 * c1) - (b0 * b0 + d * b1 * b1)
        D1 = 4 * (a0 * c1 + a1 * c0) - 2 * b0 * b1
        if D0 == 0 and D1 == 0:
            continue
        nondeg.append(((a0, a1), (b0, b1), (c0, c1)))
        if pos_L(c0, c1, d) and pos_L(-c0, -c1, d) and \
           pos_L(D0, D1, d) and pos_L(-D0, -D1, d):
            pd.append(((a0, a1), (b0, b1), (c0, c1), A, B))
    print(f"  positive definite (both embeddings): {len(pd)}")
    for rec in pd[:10]:
        print("   ", rec)
    print(f"  nondegenerate forms: {len(nondeg)}")
    for rec in nondeg[:10]:
        print("   ", rec)
    return found, pd


if __name__ == "__main__":
    mode = sys.argv[1]
    d = int(sys.argv[2])
    spec = sys.argv[3]
    H = int(sys.argv[4])
    run(mode, d, spec, H)
