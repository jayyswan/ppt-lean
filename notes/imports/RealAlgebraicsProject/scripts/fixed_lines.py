"""Session 12: which abelian subgroups A of PSL(2,8), A_9, S_9 fix a line on Q4?

A line on Q4 (a 2-plane in V on which Q4 = 6 p4 - p2^2 vanishes identically) that is
A-invariant is a sum of its intersections with the isotypic components of V.  So it is
(a) a 2-plane inside one isotypic component V_chi, or
(b) span(u, v) with u in V_chi, v in V_psi, chi != psi.
For (b), the coefficient of x^i y^(4-i) in Q4(xu + yv) transforms by chi^i psi^(4-i), so only
coefficients with chi^i psi^(4-i) = 1 can be nonzero.  We solve the surviving equations
numerically (complex Gauss-Newton from random starts in random affine charts).
Input: abel.txt from abel.g (GAP).  Output: per group, a witness line or 'NONE FOUND'.
"""
import ast, itertools, sys
import numpy as np

rng = np.random.default_rng(int(__import__("os").environ.get("SEED","12")))
N = 9

def perm_mat(p):
    M = np.zeros((N, N))
    for i, j in enumerate(p):
        M[j - 1, i] = 1.0
    return M

def closure(gens):
    elems = {tuple(range(1, N + 1)): ()}
    frontier = [tuple(range(1, N + 1))]
    words = {tuple(range(1, N + 1)): (0,) * len(gens)}
    orders = []
    for g in gens:
        o, q = 1, tuple(g)
        while q != tuple(range(1, N + 1)):
            q = tuple(g[x - 1] for x in q); o += 1
        orders.append(o)
    # abelian: enumerate exponent vectors
    out = []
    for ex in itertools.product(*[range(o) for o in orders]):
        p = list(range(1, N + 1))
        for g, e in zip(gens, ex):
            for _ in range(e):
                p = [g[x - 1] for x in p]
        out.append((ex, tuple(p)))
    return orders, out

# orthonormal basis of V (trace zero) in C^9
B = np.linalg.qr(np.vstack([np.ones(N), np.eye(N)[:-1]]).T)[0][:, 1:]  # 9 x 8

def Q4(x):
    return 6 * np.sum(x ** 4) - np.sum(x ** 2) ** 2

def coeffs(u, v):
    # coefficients of Q4(x u + y v) as a quartic in (x, y): sample 5 values of y/x
    ts = np.exp(2j * np.pi * np.arange(5) / 5)
    vals = np.array([Q4(u + t * v) for t in ts])
    # vals_k = sum_i c_i t_k^i, with c_i the coefficient of x^(4-i) y^i
    return np.fft.fft(vals) / 5 * 1.0  # c_i = (1/5) sum_k vals_k t_k^{-i}

def isotypic(gens):
    orders, elems = closure(gens)
    mats = {ex: B.T @ perm_mat(p) @ B for ex, p in elems}
    comps = []
    for chi in itertools.product(*[range(o) for o in orders]):
        P = np.zeros((8, 8), dtype=complex)
        for ex, M in mats.items():
            val = np.exp(2j * np.pi * sum(c * e / o for c, e, o in zip(chi, ex, orders)))
            P += np.conj(val) * M
        P /= len(elems)
        U, s, _ = np.linalg.svd(P)
        d = int(np.sum(s > 0.5))
        if d:
            comps.append((chi, B @ U[:, :d]))  # basis in C^9 coordinates
    return orders, comps

def char_pow_trivial(chis, exps, orders):
    tot = [0] * len(orders)
    for chi, e in zip(chis, exps):
        tot = [(t + c * e) % o for t, c, o in zip(tot, chi, orders)]
    return all(t == 0 for t in tot)

def solve(build, nvar, eqmask, tries=40):
    """build(z) -> (u, v); minimise the masked coefficients by Gauss-Newton."""
    best = np.inf
    for _ in range(tries):
        z = rng.normal(size=nvar) + 1j * rng.normal(size=nvar)
        for it in range(80):
            u, v = build(z)
            F = coeffs(u, v)[eqmask]
            r = np.linalg.norm(F) / (np.linalg.norm(u) * np.linalg.norm(v)) ** 2
            if r < 1e-13:
                break
            h = 1e-7
            J = np.zeros((len(F), nvar), dtype=complex)
            for k in range(nvar):
                dz = np.zeros(nvar, dtype=complex); dz[k] = h
                J[:, k] = (coeffs(*build(z + dz))[eqmask] - F) / h
            step = np.linalg.lstsq(J, -F, rcond=None)[0]
            z = z + step
        best = min(best, r)
        if r < 1e-11:
            u, v = build(z)
            return r, u, v
    return best, None, None

def fixed_line(gens):
    orders, comps = isotypic(gens)
    reports = []
    for (chi, Bc) in comps:  # case (a)
        d = Bc.shape[1]
        if d < 2:
            continue
        if not char_pow_trivial([chi], [4], orders):
            return ("whole eigenspace, chi^4 != 1", chi, d)
        R = np.linalg.qr(rng.normal(size=(d, d)) + 1j * rng.normal(size=(d, d)))[0]
        Bc2 = Bc @ R
        if d == 2:
            F = coeffs(Bc2[:, 0], Bc2[:, 1])
            if np.linalg.norm(F) < 1e-9:
                return ("eigenspace of dim 2 on Q4", chi, d)
            continue
        def build(z, Bc2=Bc2, d=d):
            M = z.reshape(2, d - 2)
            return Bc2[:, 0] + Bc2[:, 2:] @ M[0], Bc2[:, 1] + Bc2[:, 2:] @ M[1]
        r, u, v = solve(build, 2 * (d - 2), np.ones(5, bool), tries=int(__import__("os").environ.get("TRIES","40")))
        if u is not None:
            return ("2-plane in eigenspace", chi, d, r)
    for (c1, B1), (c2, B2) in itertools.combinations(comps, 2):  # case (b)
        mask = np.array([char_pow_trivial([c1, c2], [4 - i, i], orders) for i in range(5)])
        d1, d2 = B1.shape[1], B2.shape[1]
        R1 = np.linalg.qr(rng.normal(size=(d1, d1)) + 1j * rng.normal(size=(d1, d1)))[0]
        R2 = np.linalg.qr(rng.normal(size=(d2, d2)) + 1j * rng.normal(size=(d2, d2)))[0]
        B1r, B2r = B1 @ R1, B2 @ R2
        if not mask.any():
            return ("no surviving coefficient", c1, c2)
        nvar = (d1 - 1) + (d2 - 1)
        def build(z, B1r=B1r, B2r=B2r, d1=d1):
            return B1r[:, 0] + B1r[:, 1:] @ z[:d1 - 1], B2r[:, 0] + B2r[:, 1:] @ z[d1 - 1:]
        if nvar == 0:
            F = coeffs(B1r[:, 0], B2r[:, 0])[mask]
            if np.linalg.norm(F) < 1e-9:
                return ("pair of eigenvectors", c1, c2)
            continue
        r, u, v = solve(build, nvar, mask, tries=int(__import__("os").environ.get("TRIES","25")))
        if u is not None:
            return ("u in V_chi, v in V_psi", c1, c2, (d1, d2), mask.sum(), r)
    return None

if __name__ == "__main__":
    lines = open(sys.argv[1] if len(sys.argv) > 1 else "abel.txt").read().split("\n")
    for ln in lines:
        if not ln.strip():
            continue
        name, size, struct, gens = ln.split(";")
        gens = ast.literal_eval(gens)
        res = fixed_line(gens)
        orbs = sorted(len(o) for o in orbits(gens)) if False else ""
        print(f"{name:6s} {size:>4s} {struct:22s} {gens}  ->  {res if res else 'NONE FOUND'}", flush=True)
