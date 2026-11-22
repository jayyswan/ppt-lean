# Geometry of the nine points P_i = (a_i, b_i) in C^2 for a line on D: collinear triples, conics through 6, cubic pencil.
import numpy as np, itertools as it
X = np.load('dlines.npy')
for row in X:
    a, b = row[:9], row[9:]
    pts = np.stack([a, b, np.ones(9)], 1)
    col = [t for t in it.combinations(range(9), 3) if abs(np.linalg.det(pts[list(t)])) < 1e-6*np.abs(pts).max()**2]
    def conic_row(p): x, y, z = p; return [x*x, x*y, y*y, x*z, y*z, z*z]
    con6 = 0
    for s in it.combinations(range(9), 6):
        M = np.array([conic_row(pts[i]) for i in s]); sv = np.linalg.svd(M, compute_uv=False)
        if sv[-1] < 1e-6*sv[0]: con6 += 1
    print('collinear triples:', len(col), col[:6], '| 6-subsets on a conic:', con6)
