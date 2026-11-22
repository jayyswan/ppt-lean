# Session 39: monodromy of the 9 roots of G(x;U) (fixed h = x^3+a x+b) around each root of A, B and around U=infinity.
# Loops: from base point U0, straight segment to a small circle around the branch point, circle once ccw, back.
# usage: python3 xh_mono.py a b [U0re U0im] [rad]
import sys, numpy as np, cypari; P = cypari.pari
for l in open('EngineO.gp'):
    l = l.strip()
    if l and not l.startswith('\\\\'): P(l)
a, b = sys.argv[1], sys.argv[2]
U0 = complex(float(sys.argv[3]), float(sys.argv[4])) if len(sys.argv) > 4 else complex(0.3, 0.7)
rad = float(sys.argv[5]) if len(sys.argv) > 5 else 1e-3
P(f'Gh=substvec(G,[a,b],[({a}),({b})]); Bh=substvec(Bu,[a,b],[({a}),({b})]); Ah=substvec(Au,[a,b],[({a}),({b})])')
# coefficient matrix: coeffs of x^9..x^0 as polys in U
C = []
for k in range(9, -1, -1):
    pk = P(f'polcoef(Gh,{k},x)')
    C.append([float(P('polcoef')(pk, j, P('U'))) for j in range(6)])
C = np.array(C)  # 10 x 6
def coeffs(U):
    pw = np.array([U**j for j in range(6)])
    return C @ pw
def roots(U): return np.roots(coeffs(U))
def track(path, r):
    r = r.copy()
    for U in path[1:]:
        nr = roots(U)
        # match greedily via assignment on distance
        from scipy.optimize import linear_sum_assignment
        Dm = np.abs(r[:, None] - nr[None, :])
        i, j = linear_sum_assignment(Dm)
        r = nr[j[np.argsort(i)]]
    return r
def seg(z0, z1, n): return [z0 + (z1 - z0) * t for t in np.linspace(0, 1, n)]
def loop(c, rad, n=4000):
    d = (U0 - c); d = d / abs(d)
    s = c + rad * d
    path = seg(U0, s, n) + [c + rad * d * np.exp(2j * np.pi * t) for t in np.linspace(0, 1, n)] + seg(s, U0, n)
    return path
def perm(path, r0):
    r1 = track(path, r0)
    p = [int(np.argmin(np.abs(r0 - z))) for z in r1]
    return p
def cyc(p):
    seen = set(); out = []
    for i in range(len(p)):
        if i in seen: continue
        j = i; L = 0
        while j not in seen: seen.add(j); j = p[j]; L += 1
        out.append(L)
    return sorted(out, reverse=True)
r0 = roots(U0)
print('U0', U0, 'min root sep', min(abs(r0[i]-r0[j]) for i in range(9) for j in range(i)))
br = []
for name, pol in (('A', 'Ah'), ('B', 'Bh')):
    for z in P(f'polroots({pol})'):
        br.append((name, complex(float(P('real')(z)), float(P('imag')(z)))))
perms = []
for name, c in br:
    p = perm(loop(c, rad), r0)
    perms.append(p)
    print(name, np.round(c, 4), 'cycle type', cyc(p), p)
# loop at infinity: big circle |U| = R (cw relative to finite points, we do ccw)
R = 3 * max(abs(c) for _, c in br) + 10
path = seg(U0, U0 / abs(U0) * R, 6000) + [R * (U0 / abs(U0)) * np.exp(2j * np.pi * t) for t in np.linspace(0, 1, 20000)] + seg(U0 / abs(U0) * R, U0, 6000)
pinf = perm(path, r0)
print('big ccw circle: cycle type', cyc(pinf), pinf)
# genus by Riemann-Hurwitz with the finite perms and the infinity perm
tot = sum(9 - len(cyc(p)) for p in perms) + (9 - len(cyc(pinf)))
print('sum (e-1) incl. infinity =', tot, ' genus =', (tot - 18) / 2 + 1)
import pickle; pickle.dump((U0, r0, br, perms, pinf), open(f'mono_{a}_{b}.pkl', 'wb'))
