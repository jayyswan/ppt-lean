# r = 5: structure of real lines in V_3 and the sign of p4 on them
import sys, numpy as np
sys.argv = ['v4chain.py', '5', '0', sys.argv[1] if len(sys.argv) > 1 else '3']
src = open('v4chain.py').read().split("\ntot_real_C")[0]
exec(src)
np.set_printoptions(precision=4, suppress=True, linewidth=150)
signs = []; mins = []
for q in range(int(6)):
    Q = v3_point(); E = frame(Q); A1, A2, C3, Z = forms(Q, E)
    pts = cq_points(A1, A2, C3, 60)
    for t in pts[:20]:
        v = E @ t
        _, co = p4_roots(Q, v)
        # min of p4 on the projective line, normalised: p4(cos a Q + sin a v)/|.|^4
        a = np.linspace(0, np.pi, 721)
        vals = [psum(zc(np.cos(x) * Q + np.sin(x) * v), 4) / np.linalg.norm(np.cos(x) * Q + np.sin(x) * v) ** 4 for x in a]
        mins.append(min(vals)); signs.append(np.sign(min(vals)) * np.sign(max(vals)))
    if q == 0 and pts:
        v = E @ pts[0]
        print('zQ =', zc(Q)); print('zv =', zc(v))
print('lines:', len(mins), ' p4 sign constant on all:', all(s > 0 for s in signs), ' min of p4 (normalised) over lines: %.3g' % min(mins), ' max of mins %.3g' % max(mins))
