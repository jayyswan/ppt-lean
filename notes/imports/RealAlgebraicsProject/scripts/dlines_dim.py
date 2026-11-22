# Is the family of lines on D really 3-dimensional, or 1-dimensional with an obstructed (3-dim) tangent space?
# Test: with k random linear slices on the 12 gauge-fixed coordinates, solutions exist for all random slices iff dim >= k.
import numpy as np, sys
sys.argv = ['x', '23']
exec(open('s18_lines.py').read().split("for kind, nslice")[0])
for k in [1, 2, 3, 4]:
    ok = 0; resid_min = []
    for trial in range(40):
        x = solve('D', k)
        if x is None: continue
        a, b = vec(x[:8]), vec(x[8:])
        if any(abs(a[i]-a[j]) + abs(b[i]-b[j]) < 1e-6 for i in range(9) for j in range(i+1, 9)): continue
        ok += 1
    print('slices', k, ': nondegenerate solutions in 40 starts =', ok)
