"""Session 33. Group law on a plane cubic (exact chord/tangent formulas) and the class
of D - 3H for D = the 9 points.  Origin O = first point; T = tangential of O.
sum_i p_i (+) = 3T  <=>  D ~ 3H.  Prints min over k<=KMAX of dist(k*A, k*B)."""
import numpy as np, itertools
def monos(d): return [e for e in itertools.product(range(d + 1), repeat=3) if sum(e) == d]
M3 = monos(3)
def F(cf, x): return sum(c * np.prod(x ** np.array(e)) for c, e in zip(cf, M3))
def grad(cf, x):
    g = np.zeros(3, dtype=complex if np.iscomplexobj(x) else float)
    for c, e in zip(cf, M3):
        for j in range(3):
            if e[j]:
                ee = list(e); ee[j] -= 1; g[j] += c * e[j] * np.prod(x ** np.array(ee))
    return g
def nz(x): x = x / np.linalg.norm(x); i = np.argmax(abs(x)); return x * np.sign(x[i])
def third(cf, a, b):
    if np.linalg.norm(np.cross(nz(a), nz(b))) < 1e-9:  # tangent at a
        g = grad(cf, a); t = np.cross(a, g); t = nz(np.cross(a, np.cross(g, t)) if False else t)
        # t is orthogonal to g? cross(a,g) is orthogonal to g: yes
        u = -(grad(cf, t) @ a) / F(cf, t); return nz(a + u * t)
    u = -(grad(cf, a) @ b) / (grad(cf, b) @ a); return nz(a + u * b)
def add(cf, O, a, b): return third(cf, O, third(cf, a, b))
def dist(a, b): return np.linalg.norm(np.cross(nz(a), nz(b)))
def class_test(cf, pts, KMAX=12):
    O = nz(pts[0]); T = third(cf, O, O)
    A = O
    for p in pts: A = add(cf, O, A, nz(p))
    B = add(cf, O, add(cf, O, T, T), T)
    out = []; kA, kB = A, B
    for k in range(1, KMAX + 1):
        out.append(dist(kA, kB)); kA = add(cf, O, kA, A); kB = add(cf, O, kB, B)
    return np.array(out)
if __name__ == '__main__':
    rng = np.random.default_rng(0); a, b = -2.0, 1.5
    cf = np.zeros(10)
    for c, e in [(1, (3, 0, 0)), (a, (1, 0, 2)), (b, (0, 0, 3)), (-1, (0, 2, 1))]: cf[M3.index(e)] += c
    def on(x, s): return np.array([x, s * np.sqrt(x ** 3 + a * x + b), 1.0])
    # D ~ 3H: three lines, each through two random points -> third
    pts = []
    for _ in range(3):
        p, q = on(*rng.uniform(1.4, 4, 1), 1), on(*rng.uniform(1.4, 4, 1), -1)
        pts += [p, q, third(cf, p, q)]
    print('3 lines (expect 0 at k=1):', class_test(cf, pts, 4))
    pts = [on(x, s) for x, s in zip(rng.uniform(1.4, 4, 9), rng.choice([-1, 1], 9))]
    print('random (expect O(1)):', np.round(class_test(cf, pts, 6), 3))
