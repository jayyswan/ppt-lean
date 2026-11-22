import numpy as np, sys
sys.argv = ['x', '31']
exec(open('s18_lines.py').read().split("for kind, nslice")[0])
def rank(M, tol=1e-7):
    s = np.linalg.svd(M, compute_uv=False); return int(np.sum(s > tol*s[0])), s
ok3 = 0
for trial in range(120):
    if solve('D', 3) is not None: ok3 += 1
print('3 slices, 120 starts: solutions', ok3)
lines = []
for trial in range(60):
    x = solve('D', 2)
    if x is None: continue
    a, b = vec(x[:8]), vec(x[8:])
    if any(abs(a[i]-a[j]) + abs(b[i]-b[j]) < 1e-6 for i in range(9) for j in range(i+1, 9)): continue
    one = np.ones(9)
    r6, s6 = rank(np.array([one, a, b, a*a, a*b, b*b]))
    r10, s10 = rank(np.array([one, a, b, a*a, a*b, b*b, a**3, a*a*b, a*b*b, b**3]))
    # p2 on the line and q2 (needs m_k): skip; record ranks
    lines.append((a, b))
    print('rank[1,a,b,a2,ab,b2] =', r6, 'smallest sv %.1e' % s6[-1], '| rank with cubes =', r10, 'smallest sv %.1e' % s10[-1])
    if len(lines) >= 6: break
np.save('dlines.npy', np.array([np.concatenate([a, b]) for a, b in lines]))
