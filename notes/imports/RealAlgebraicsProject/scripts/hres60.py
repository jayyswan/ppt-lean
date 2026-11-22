# hres60.py -- session 60: P-points of H_E = {25 p3 p7 = 21 p5^2} (centred tau) for r = 9 via the
# tangent-residual octic at points of L_135 = {p1 = p3 = p5 = 0} (S59.3, now with P-valued dials).
# For N random real totally real points tau0 of L_135 (Newton) and M random tangent directions v
# (sum v = 0, sum tau0^2 v = 0): residual octic h(t)/t^2, h = 25 p3 p7 - 21 p5^2 on tau0 + t v.
# Prints the distribution of real-root counts, and for real residual roots: p3 (cubic cofactor
# nondegenerate), the auxiliary cubic z (e1 = 0, e3 = -p3/3, e2 = p5/(5 e3)), its real roots,
# and the shape invariants of the even power sums of the 12 points (tau, z).
# Then the shape invariants (I3, I4) of the virtual sextic (affine invariants of the 6 values v with
# power sums p_{2m}(tau, z)/2): ranges, quantiles, distance to T_6's (0, 3/2).
# Usage: python3 hres60.py <seed> <N> <M>   (seconds; runs used: 1 20 20, 2 30 20)
import sys, numpy as np
seed, N, M = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = np.random.default_rng(seed)
ps = lambda y, k: np.sum(y**k)
def l135(y0):
    y = y0.copy()
    for _ in range(100):
        F = np.array([ps(y,1), ps(y,3), ps(y,5)]); J = np.array([np.ones(9), 3*y**2, 5*y**4])
        dy = np.linalg.lstsq(J, -F, rcond=None)[0]; y += dy
        if np.linalg.norm(dy) < 1e-14: break
    return y if np.linalg.norm([ps(y,1), ps(y,3), ps(y,5)]) < 1e-10 else None
def h_poly(t0, v):
    # coefficients of h(t) = 25 p3 p7 - 21 p5^2 along t0 + t v, via sampling (degree 10)
    ts = np.linspace(-1, 1, 11) * 0.5
    vals = [25*ps(t0+t*v,3)*ps(t0+t*v,7) - 21*ps(t0+t*v,5)**2 for t in ts]
    return np.polyfit(ts, vals, 10)
from collections import Counter
cnt = Counter(); rows = []; EV = []
for i in range(N):
    y = None
    while y is None: y = l135(rng.normal(size=9))
    for j in range(M):
        A = np.array([np.ones(9), y**2]); v = rng.normal(size=9)
        v -= A.T @ np.linalg.lstsq(A.T, v, rcond=None)[0]   # project to sum v = 0, sum y^2 v = 0
        c = h_poly(y, v)
        oc = np.polydiv(c, [1, 0, 0])
        res = oc[0]; rem = np.max(np.abs(oc[1])) / np.max(np.abs(c))
        rts = np.roots(res); rr = rts[np.abs(rts.imag) < 1e-7 * (1 + np.abs(rts.real))].real
        cnt[len(rr)] += 1
        for t in rr:
            tau = y + t*v; tau -= tau.mean()
            p3, p5, p7 = ps(tau,3), ps(tau,5), ps(tau,7)
            e3 = -p3/3; e2 = p5/(5*e3); z = np.roots([1, 0, e2, -e3])
            allp = np.concatenate([tau, z])
            odd = [abs(np.sum(allp**k)) for k in (1,3,5,7)]
            ev = [np.sum(allp**k).real for k in (2,4,6,8)]
            nz = int(np.sum(np.abs(z.imag) < 1e-9))
            rows.append((i, j, t, rem, p3, nz, max(odd)/np.max(np.abs(tau))**7, ev[1]/ev[0]**2, ev[2]/ev[0]**3, ev[3]/ev[0]**4)); EV.append((ev, nz))
print('real-root counts of residual octic:', dict(sorted(cnt.items())))
print('i j t  rem(t^2|h)  p3  #real z  odd-check  P4/P2^2 P6/P2^3 P8/P2^4')
for r in rows[:12]: print(r[0], r[1], '%.4f %.1e %.3f %d %.1e %.4f %.4f %.4f' % r[2:])
print('total residual real points', len(rows))
# --- shape invariants of the virtual sextic: v-power sums mu_m = p_{2m}(tau, z)/2 (6 values);
# central moments k2, k3, k4; I3 = k3^2/k2^3, I4 = k4/k2^2.  T_6: (I3, I4) = (0, 3/2).
def inv(ev):
    m = [1.0] + [e/12 for e in ev]
    k2 = m[2] - m[1]**2; k3 = m[3] - 3*m[1]*m[2] + 2*m[1]**3
    k4 = m[4] - 4*m[1]*m[3] + 6*m[1]**2*m[2] - 3*m[1]**4
    return k3**2/k2**3, k4/k2**2, k2
J = np.array([inv(e)[:2] for e, nz in EV]); K2 = np.array([inv(e)[2] for e, nz in EV]); NZ = np.array([nz for e, nz in EV])
print('points', len(J), 'k2 > 0:', int(np.sum(K2 > 0)))
for lab, mask in (('3 real z', NZ == 3), ('1 real z', NZ == 1)):
    j = J[mask]
    if len(j): print(lab, len(j), 'I3 quantiles', np.round(np.quantile(j[:,0], [0,.1,.5,.9,1]), 3), ' I4 quantiles', np.round(np.quantile(j[:,1], [0,.1,.5,.9,1]), 3))
print('closest to T_6 (0, 1.5):', np.round(np.sort(np.hypot(J[:,0], J[:,1] - 1.5))[:5], 4))
