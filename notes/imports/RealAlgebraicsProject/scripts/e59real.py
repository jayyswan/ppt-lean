# Real test for S59.4: crossings of the Bezier (alpha t^2+beta, Y(t)) with a rational sextic graph y = S(u).
# Counts members of S(alpha t^2 + beta) - Y(t) (degree 12) with >= 9 real roots, for random real dials.
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
T6 = np.polynomial.chebyshev.cheb2poly([0]*6+[1])[::-1]          # T_6, highest first
U6 = np.array([1,0,0,0,0,0,0.])                                  # u^6
U33 = np.polymul(np.poly([0,0,0]), np.poly([1,1,1]))            # u^3 (u-1)^3
def count(S, trials, scale):
    hist = {}
    for _ in range(trials):
        a, b = rng.normal(), rng.normal()
        if S is T6: a, b = 2 + scale*rng.normal(), -1 + scale*rng.normal()
        q = np.poly1d([a, 0, b]); g = np.poly1d([0.])
        for i, c in enumerate(S): g = g + c * q**(6 - i)
        Y = np.poly1d(rng.normal(size=4) * scale)
        r = (g - Y).roots
        nr = int(np.sum(np.abs(r.imag) < 1e-7 * (1 + np.abs(r))))
        hist[nr] = hist.get(nr, 0) + 1
    return dict(sorted(hist.items()))
print('T_6, dials near (2,-1), small Y:', count(T6, 4000, 0.1))
print('T_6, dials near (2,-1), Y scale 0.5:', count(T6, 4000, 0.5))
print('u^6, random dials:', count(U6, 4000, 1.0))
print('u^3(u-1)^3, random dials:', count(U33, 4000, 1.0))
