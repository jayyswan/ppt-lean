# Refine D-lines to 60 digits (mpmath Newton on the 11 coefficient equations + gauge + 2 slices fixed at the found point),
# then recompute the singular values of [1, a, b, a^2, ab, b^2, a^3, a^2 b, a b^2, b^3] (9 x 10).
import numpy as np, mpmath as mp
mp.mp.dps = 60
X = np.load('dlines.npy')
def vecm(u): return [-mp.fsum(u)] + list(u)
def coeffs_m(f, deg, a, b):
    out = []
    for k in range(deg+1):
        pass
    ts = [mp.exp(2j*mp.pi*j/(deg+1)) for j in range(deg+1)]
    vals = [f([ai + t*bi for ai, bi in zip(a, b)]) for t in ts]
    return [mp.fsum(vals[j]*mp.exp(-2j*mp.pi*j*k/(deg+1)) for j in range(deg+1))/(deg+1) for k in range(deg+1)]
P = lambda z, k: mp.fsum(zi**k for zi in z)
Q4 = lambda z: 6*P(z,4) - P(z,2)**2
Q5 = lambda z: 18*P(z,5) - 5*P(z,2)*P(z,3)
for row in X:
    a0, b0 = row[:9], row[9:]
    # gauge: a has u-coords (1,0,...), b has (0,1,...) already (from solve); unknowns y = 12 free coords
    y = [mp.mpc(c) for c in np.concatenate([a0[3:], b0[3:]])]
    rng = np.random.default_rng(0); L = [[mp.mpc(*rng.normal(size=2)) for _ in range(12)] for _ in range(2)]
    c = [mp.fsum(L[i][j]*y[j] for j in range(12)) for i in range(2)]
    def F(y):
        a = vecm([1, 0] + y[:6]); b = vecm([0, 1] + y[6:])
        return coeffs_m(Q4, 4, a, b) + coeffs_m(Q5, 5, a, b) + [mp.fsum(L[i][j]*y[j] for j in range(12)) - c[i] for i in range(2)]
    for it in range(12):
        f = F(y); J = mp.matrix(13, 12); h = mp.mpf(10)**-30
        for j in range(12):
            yy = list(y); yy[j] += h; fj = F(yy)
            for i in range(13): J[i, j] = (fj[i] - f[i])/h
        # least squares Newton step
        Jt = J.H; dy = mp.lu_solve(Jt*J, -(Jt*mp.matrix(f)))
        y = [y[j] + dy[j] for j in range(12)]
    res = max(abs(v) for v in F(y))
    a = vecm([1, 0] + y[:6]); b = vecm([0, 1] + y[6:])
    M = mp.matrix([[1]*9, a, b, [ai*ai for ai in a], [ai*bi for ai, bi in zip(a, b)], [bi*bi for bi in b],
                   [ai**3 for ai in a], [ai*ai*bi for ai, bi in zip(a, b)], [ai*bi*bi for ai, bi in zip(a, b)], [bi**3 for bi in b]])
    sv = mp.svd_c(M, compute_uv=False)
    print('residual %.1e' % float(res), '| two smallest sv of 10x9 moment matrix:', mp.nstr(sv[7], 5), mp.nstr(sv[8], 5))
