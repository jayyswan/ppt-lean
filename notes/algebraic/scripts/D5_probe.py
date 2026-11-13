"""D5: does the good surface S pass through a given line l0 of X?  (Branch probe.)
X = {p1 = p3 = p5 = 0} in P^8.  Chart of G(2,9) at l0 = span(u0, v0): u = u0 + N a, v = v0 + N b,
N a basis (9 x 7) of a complement of l0: 14 unknowns.  Equations: coefficients of p1, p3, p5 on l (2+4+6 = 12)
plus two linear slices L1.z = eps*c1, L2.z = eps*c2.  Newton from z0 = eps * random.  A solution is GOOD if
p7|_l is not identically 0 (pairing lines and the 9th-root cosine lines have p7|_l = 0).
If l0 lies on S, good solutions appear at distance ~ eps for every eps.  If not, good solutions near l0 vanish
as eps -> 0.
"""
import sys
import numpy as np
from math import comb

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)


def chart(u0, v0):
    M = np.vstack([u0, v0])
    _, _, vh = np.linalg.svd(M)
    return vh[2:].conj().T              # 9 x 7, orthonormal complement


def lines(z, u0, v0, N):
    return u0 + N @ z[:7], v0 + N @ z[7:]


def eqs(z, u0, v0, N):
    u, v = lines(z, u0, v0, N)
    out = []
    for d in (1, 3, 5):
        for j in range(d + 1):
            out.append(comb(d, j) * np.sum(u ** (d - j) * v ** j))
    return np.array(out)


def p7(z, u0, v0, N):
    u, v = lines(z, u0, v0, N)
    m = max(np.abs(u).max(), np.abs(v).max())
    u, v = u / m, v / m
    return max(abs(comb(7, j) * np.sum(u ** (7 - j) * v ** j)) for j in range(8))


def nj(f, z, h=1e-8):
    f0 = f(z)
    J = np.zeros((len(f0), len(z)), complex)
    for k in range(len(z)):
        e = np.zeros(len(z), complex); e[k] = h
        J[:, k] = (f(z + e) - f0) / h
    return J


def probe(u0, v0, eps_list=(1e-1, 3e-2, 1e-2, 3e-3, 1e-3), nst=150):
    N = chart(u0, v0)
    L = rng.normal(size=(2, 14)) + 1j * rng.normal(size=(2, 14))
    c = rng.normal(size=2) + 1j * rng.normal(size=2)
    res = []
    for eps in eps_list:
        f = lambda z: np.concatenate([eqs(z, u0, v0, N), L @ z - eps * c])
        best = np.inf
        ngood = 0
        for _ in range(nst):
            z = eps * (rng.normal(size=14) + 1j * rng.normal(size=14)) * rng.choice([0.5, 1, 3])
            for it in range(60):
                fz = f(z)
                if np.linalg.norm(fz) < 1e-13:
                    break
                z = z + np.linalg.lstsq(nj(f, z), -fz, rcond=None)[0]
                if np.linalg.norm(z) > 10:
                    break
            if np.linalg.norm(f(z)) < 1e-11 and np.linalg.norm(z) < 10:
                if p7(z, u0, v0, N) > 1e-7:
                    ngood += 1
                    best = min(best, np.linalg.norm(z))
        res.append((eps, ngood, best))
    return res


def pairing_line(A, B):
    """Lambda_pi: y = (a, -a, b, -b, c, -c, d, -d, 0)."""
    emb = lambda w: np.array([w[0], -w[0], w[1], -w[1], w[2], -w[2], w[3], -w[3], 0], complex)
    return emb(A), emb(B)


if __name__ == "__main__":
    kind = sys.argv[2]
    if kind == "control-good":
        # a good line from the D5 sigma11 run
        ns = {}
        exec(open('D5_s11lines.py').read().split('sols = []')[0].replace('seed, nst = int(sys.argv[1]), int(sys.argv[2])', 'seed, nst = 0, 0'), ns)
        import glob
        z = np.load(sorted(glob.glob('s11_seed*.npy'))[0])[0]
        Wg = ns['W']
        u0 = Wg[0] + z[:5] @ Wg[2:]; v0 = Wg[1] + z[5:] @ Wg[2:]
    elif kind == "control-generic-Y":
        u0, v0 = pairing_line(rng.normal(size=4) + 1j * rng.normal(size=4), rng.normal(size=4) + 1j * rng.normal(size=4))
    else:
        A = np.array(eval(sys.argv[3]), complex); B = np.array(eval(sys.argv[4]), complex)
        u0, v0 = pairing_line(A, B)
    for eps, ng, best in probe(u0, v0):
        print(f"{kind}: eps {eps:.0e}  good solutions {ng:3d}  nearest good |z| = {best:.3e}  ratio {best/eps:.2f}")
