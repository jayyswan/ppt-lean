# Degree of R_20(v) = Res_kappa(Q4(P+kv), p5(P+kv)) along a line v = v0 + t v1 in N_P-directions (no B_P condition needed
# for the degree count; it is a polynomial in v). 60-digit mpmath; P generic / in L_135 / in Y4 (from w60.py samplers).
import sys; sys.path.insert(0,'.')
from w60 import *
import mpmath as mp
mp.mp.dps = 60
def coeffs(P, v, k):
    # coefficients in kappa of p_k(P + kappa v), as mp numbers
    from math import comb
    return [sum(comb(k, j)*P[i]**(k-j)*v[i]**j for i in range(9)) for j in range(k+1)]
def polmul(a, b):
    c = [mp.mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j] += x*y
    return c
def R(P, v):
    p2, p4, p5 = coeffs(P,v,2), coeffs(P,v,4), coeffs(P,v,5)
    q4 = [6*x for x in p4]; sq = polmul(p2, p2)
    q4 = [q4[j]-sq[j] for j in range(5)]
    f, g = q4[::-1], p5[::-1]          # highest degree first
    m, n_ = 4, 5; N = m+n_
    S = mp.zeros(N, N)
    for i in range(n_):
        for j in range(m+1): S[i, i+j] = f[j]
    for i in range(m):
        for j in range(n_+1): S[n_+i, i+j] = g[j]
    return mp.det(S)
for kind in ['gen', 'L135', 'Y4']:
    P = real_X_point(3)
    if kind == 'L135': P = newton_real(P, [lambda z: ps(z,3), lambda z: ps(z,5)])
    if kind == 'Y4': P = newton_real(P, [lambda z: ps(z,3), lambda z: Q4(z)])
    Pm = [mp.mpf(x) for x in P]
    B = NP_basis(P); r = np.random.default_rng(5)
    v0 = [mp.mpf(x) for x in B @ r.normal(size=6)]; v1 = [mp.mpf(x) for x in B @ r.normal(size=6)]
    ts = [mp.mpf(k)/7 for k in range(-15, 16)]   # 31 points
    vals = [R(Pm, [v0[i]+t*v1[i] for i in range(9)]) for t in ts]
    # fit degree 30 interpolant; report size of coefficients by degree
    V = mp.matrix([[t**j for j in range(31)] for t in ts]); c = mp.lu_solve(V, mp.matrix(vals))
    top = max(abs(c[j]) for j in range(31))
    print(kind, 'p5(P)=%.2e Q4(P)=%.2e' % (ps(P,5), Q4(P)), 'coef ratios deg 18..24:', ['%.1e' % (abs(c[j])/top) for j in range(18,25)])
