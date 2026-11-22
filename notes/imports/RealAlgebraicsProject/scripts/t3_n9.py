"""T3 odd-Tschirnhaus chain at n = 9, totally real case, in y-space.
Steps: (1) cubic -> P on X={p1=p3=0}; (2) real point q0 on conic Q_P in a plane of
N_P={sum v=0, sum P^2 v=0}; (3) conic on Q_P through q0 -> sextic in t, p3(v)=0;
(4) line P+kv in X, quintic p5 -> Z in L_135.  Records simplicity margins."""
import numpy as np
rng = np.random.default_rng(1)
n = 9
p = lambda y, k: np.sum(y**k)

def poly_restrict(f, a, b, deg):
    # coefficients (high->low) of t -> f(a + t b), via sampling
    ts = np.linspace(-1, 1, deg + 1) * 1.3
    vals = [f(a + t * b) for t in ts]
    return np.polyfit(ts, vals, deg)

def simple_real_roots(c, tol=1e-7):
    r = np.roots(c)
    out = []
    dc = np.polyder(c)
    for z in r:
        if abs(z.imag) < 1e-9 * max(1, abs(z)):
            x = z.real
            out.append((x, abs(np.polyval(dc, x)) / max(1e-300, np.max(abs(c)))))
    return out

def nullspace(A):
    u, s, vt = np.linalg.svd(A)
    return vt[len(s[s > 1e-12]):].T

def run_once():
    # step 1
    E = nullspace(np.ones((1, n)))           # basis of {p1=0}
    a, b = E @ rng.normal(size=8), E @ rng.normal(size=8)
    c = poly_restrict(lambda y: p(y, 3), a, b, 3)
    rr = simple_real_roots(c)
    k, m1 = rr[rng.integers(len(rr))]
    P = a + k * b
    P /= np.linalg.norm(P)
    # step 2
    Lp = nullspace(np.vstack([np.ones(n), P**2]))   # 9x7
    QP = lambda v: np.sum(P * v * v)
    B = lambda u, w: np.sum(P * u * w)
    pl = Lp @ rng.normal(size=(7, 3))
    # real point on conic in plane span(pl): restrict to a line in the plane
    u, w = pl[:, 0], pl[:, 1] - pl[:, 2] * 0
    cq = poly_restrict(QP, u, pl[:, 1], 2)
    rq = [z.real for z in np.roots(cq) if abs(z.imag) < 1e-12]
    if not rq:
        cq = poly_restrict(QP, pl[:, 2], pl[:, 1], 2)
        rq = [z.real for z in np.roots(cq) if abs(z.imag) < 1e-12]
        u = pl[:, 2]
        if not rq:
            return None
    q0 = u + rq[0] * pl[:, 1]
    # step 3: conic through q0 in random plane of Lp
    u1, u2 = Lp @ rng.normal(size=7), Lp @ rng.normal(size=7)
    def pt(t):
        wv = u1 + t * u2
        return -QP(wv) * q0 + 2 * B(q0, wv) * wv
    ts = np.linspace(-2, 2, 7)
    c6 = np.polyfit(ts, [p(pt(t), 3) for t in ts], 6)
    r6 = simple_real_roots(c6)
    if not r6:
        return ('nosextic',)
    t0, m3 = max(r6, key=lambda z: z[1])
    v = pt(t0); v /= np.linalg.norm(v)
    # step 4
    chk = [abs(np.polyval(poly_restrict(lambda y: p(y, j), P, v, j), 0.7)) for j in (1, 3)]
    c5 = poly_restrict(lambda y: p(y, 5), P, v, 5)
    r5 = simple_real_roots(c5)
    res = []
    for kk, m4 in r5:
        Z = P + kk * v
        Z /= np.linalg.norm(Z)
        gaps = np.min(np.diff(np.sort(Z)))
        J = np.vstack([np.ones(n), 3 * Z**2, 5 * Z**4])
        sv = np.linalg.svd(J, compute_uv=False)
        q4 = 6 * p(Z, 4) - p(Z, 2)**2
        res.append(dict(gap=gaps, rank_min_sv=sv[-1], Q4=q4, m4=m4,
                        pair=min(abs(Z[i] + Z[j]) for i in range(n) for j in range(i+1, n))))
    return ('ok', m1, m3, max(chk), res, P, v)

stats = dict(ok=0, nosextic=0, fail=0)
q4s = []; best = None
for it in range(400):
    r = run_once()
    if r is None:
        stats['fail'] += 1; continue
    if r[0] == 'nosextic':
        stats['nosextic'] += 1; continue
    stats['ok'] += 1
    for d in r[4]:
        q4s.append(d['Q4'])
        if best is None or min(d['gap'], d['pair']) > min(best[1]['gap'], best[1]['pair']):
            best = (r, d)
print(stats)
q4s = np.array(q4s)
print('final points', len(q4s), 'Q4<0 fraction', np.mean(q4s < 0))
r, d = best
print('best: line-in-X residual', r[3], 'cubic margin', r[1], 'sextic margin', r[2])
print('final point: min gap', d['gap'], 'min |Zi+Zj|', d['pair'], 'Jac min sv', d['rank_min_sv'], 'quintic margin', d['m4'])
np.save('t3_best.npy', np.vstack([r[5], r[6]]))
