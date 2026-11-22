"""NOTE (session 32): as a random-start sampler this FAILS: LM is drawn into a degenerate valley
(one point at O, the other 8 colliding in 4 pairs). Kept as the record of the charge picture.
Session 32: real S_ord lines as an equipotential problem in m = 1/x.

S29.1: |F'(x_i)| = |c| h(x_i)^{5/2}.  With m = 1/x, k(m) = m^3 h(1/m) = prod(1 - e_r m):
   V_i = sum_{j!=i} log|m_i - m_j| + 1/2 log|m_i| - 5/2 log|k(m_i)|  is the same for all i,
   with m_i k(m_i) > 0 (real point of C).  Charges: +1 at each m_j, +1/2 at O (m=0),
   -5/2 at each 2-torsion point m = 1/e_r.
Usage: python3 ord_m.py <one|three> <seed> <starts>
  one  : h = (x-1)(x^2 - 2 b1 x + b1^2 + b2^2), C(R) connected, m in (0,1)
  three: h = (x-e1)(x-e2)(x-e3), 0<e1<e2<e3; unbounded comp m in (0,1/e3), egg m in (1/e2,1/e1);
         k points forced onto the egg (k = 1..8; k = 0 also tried as control)
Each hit: line z_i = (1 + s x_i)/y_i, check p1,p3,p5, conic-rank (E vs S_ord), Q4 real roots.
Writes ordm_<mode>_<seed>.npy rows: m_1..m_9, e1,e2,e3 (complex as re,im pairs for 'one': b1,b2), k
"""
import sys, numpy as np
from scipy.optimize import least_squares

mode, seed, starts = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(seed)

def kval(m, roots):
    return np.prod([1 - r * m for r in roots], axis=0)

def V(m, roots):
    d = np.abs(m[:, None] - m[None, :]); np.fill_diagonal(d, 1.0)
    return np.log(d).sum(1) + 0.5 * np.log(np.abs(m)) - 2.5 * np.log(np.abs(kval(m, roots)))

def line_check(m, roots):
    x = 1 / m
    h = np.real(np.prod([x - r for r in roots], axis=0))
    Fp = np.array([np.prod([x[i] - x[j] for j in range(9) if j != i]) for i in range(9)])
    y = np.sqrt(h) * np.sign(Fp)
    worst = 0
    for s in (0.37, -1.3, 2.1):
        z = (1 + s * x) / y; sc = np.abs(z).max()
        worst = max(worst, max(abs((z ** p).sum()) / (9 * sc ** p) for p in (1, 3, 5)))
    Z, a = 1 / y, x / y
    M = np.c_[np.ones(9), Z ** 2, Z * a, a ** 2]
    sv = np.linalg.svd(M / np.linalg.norm(M, axis=0), compute_uv=False)
    # Q4 = 6 p4 - p2^2 on the line z = Z + s a : quartic in s
    def pk(k, s): return (( Z + s * a) ** k).sum()
    ss = np.linspace(-3, 3, 9)
    vals = [6 * pk(4, s) - pk(2, s) ** 2 for s in ss]
    q = np.polyfit(ss, vals, 4)
    nreal = int(np.sum(np.abs(np.roots(q).imag) < 1e-7 * np.abs(np.roots(q)).max()))
    return worst, sv[-1] / sv[0], nreal

hits = []
for st in range(starts):
    if mode == 'one':
        b1, b2 = rng.uniform(-1.5, 1.5), rng.uniform(0.1, 2)
        roots = [1.0, complex(b1, b2), complex(b1, -b2)]
        ivs = [(0.0, 1.0)]; k = 0
        hpar = [1.0, b1, b2]
    else:
        e = np.sort(rng.uniform(0.2, 3, 3)); roots = list(e)
        k = int(rng.integers(0, 9))
        ivs = [(1 / e[1], 1 / e[0]), (0.0, 1 / e[2])]
        hpar = list(e)
    cnt = [9] if mode == 'one' else [k, 9 - k]
    def unpack(v):
        out, p = [], 0
        for (lo, hi), c in zip(ivs, cnt):
            out.append(lo + (hi - lo) * (0.5 + 0.5 * np.tanh(v[p:p + c]))); p += c
        return np.concatenate(out)
    def res(v):
        vv = np.real(V(unpack(v), roots))
        return vv - vv.mean()
    v0 = rng.normal(0, 1.5, 9)
    with np.errstate(all='ignore'):
        try:
            sol = least_squares(res, v0, method='lm', xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        except Exception:
            continue
        m = unpack(sol.x)
        r = np.abs(res(sol.x)).max() if np.all(np.isfinite(m)) else np.inf
    if not np.isfinite(r) or r > 1e-10:
        continue
    gap = np.min(np.abs(m[:, None] - m[None, :]) + np.eye(9))
    edge = min(min(np.abs(m - lo).min(), np.abs(m - hi).min()) for lo, hi in ivs)
    if gap < 1e-7 or edge < 1e-9:
        continue
    pc, cr, nq = line_check(m, roots)
    hits.append(np.r_[m, hpar, k])
    print(f"start {st}: k_egg={k} res={r:.1e} p135={pc:.1e} conicrank={cr:.1e} Q4realroots={nq} "
          f"h={np.round(hpar,3)} m={np.round(np.sort(m),5)}", flush=True)
print(f"{mode}: {len(hits)} hits / {starts} starts")
np.save(f"ordm_{mode}_{seed}.npy", np.array(hits))
