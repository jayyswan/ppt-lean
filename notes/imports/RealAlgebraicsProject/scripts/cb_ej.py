"""Session 33. The smooth cubic E_C through the 9 points [q_i] of a C_b^gen conic:
(1) its j-invariant (cross-ratio of the 4 tangent lines from one point of E_C;
    checked against a Weierstrass curve, and across 3 base points per sample);
(2) the class of D - 3H on E_C (D = the 9 points, H = line class): is k(D - 3H) = 0
    for some k <= KMAX?  Uses the exact chord/tangent group law of grp.py.
Reads cb_good.npy, cb_lab.npy (from cb_struct.py, cb_split.py); needs grp.py alongside.
Writes cb_ej.npy (columns: j, dist(kA,kB) for k = 1..KMAX).
Usage: python3 cb_ej.py [KMAX=12]   (about a minute for 205 samples)"""
import numpy as np, itertools, sys
KMAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 12
exec(open("grp.py").read().split("if __name__")[0])

def ev(coef, mons, x): return sum(c * np.prod(x ** np.array(e)) for c, e in zip(coef, mons))

def cubic_through(q):
    M = np.array([[np.prod(x ** np.array(e)) for e in M3] for x in q])
    _, s, vt = np.linalg.svd(M); return vt[-1], s[-1] / s[0], s[-2] / s[0]

def jinv(cf, P, rng):
    A, B = np.linalg.svd(P.reshape(1, 3))[2][1:]
    ss = np.linspace(-2, 2, 9); disc = []
    for s in ss:
        d = A + s * B
        us = np.array([-1, -.5, .5, 1, 1.5])
        a = np.polyfit(us, [ev(cf, M3, P + u * d) for u in us], 3)[::-1]  # a0..a3
        disc.append(a[2] ** 2 - 4 * a[1] * a[3])
    r = np.roots(np.polyfit(ss, disc, 4))
    lam = (r[0] - r[2]) * (r[1] - r[3]) / ((r[1] - r[2]) * (r[0] - r[3]))
    return 256 * (lam ** 2 - lam + 1) ** 3 / (lam ** 2 * (lam - 1) ** 2)

if __name__ == '__main__':
    rng = np.random.default_rng(0)
    if 'selftest' in sys.argv:
        a, b = -2.0, 1.5  # y^2 z = x^3 + a x z^2 + b z^3
        cf = np.zeros(10)
        for c, e in [(1, (3, 0, 0)), (a, (1, 0, 2)), (b, (0, 0, 3)), (-1, (0, 2, 1))]: cf[M3.index(e)] += c
        P = np.array([2.0, np.sqrt(8 + 2 * a + b), 1])
        print('j test', jinv(cf, P, rng), 1728 * 4 * a ** 3 / (4 * a ** 3 + 27 * b ** 2)); sys.exit()
    Qs = np.load('cb_good.npy'); lab = np.load('cb_lab.npy')
    out = []
    for Q, l in zip(Qs, lab):
        if l != 'gen': continue
        q = Q / np.linalg.norm(Q, axis=1)[:, None]
        cf, s1, s2 = cubic_through(q)
        js = [jinv(cf, q[i], rng) for i in range(3)]
        ct = class_test(cf, list(q), KMAX)
        out.append((js[0].real, max(abs(np.array(js) - js[0])) / max(1, abs(js[0])), abs(js[0].imag), ct))
    j = np.array([o[0] for o in out])
    print('n gen =', len(out), ' max j-consistency err', max(o[1] for o in out), ' max |Im j|', max(o[2] for o in out))
    print('j quantiles (0,10,25,50,75,90,100%):', np.round(np.percentile(j, [0, 10, 25, 50, 75, 90, 100]), 1))
    print('fraction j<0:', np.mean(j < 0), ' j>1728 (2 real comps):', np.mean(j > 1728), ' 0<j<1728:', np.mean((j > 0) & (j < 1728)))
    ct = np.array([o[3] for o in out])
    print('class D-3H: min over samples of dist(kA,kB), k=1..KMAX:', np.array2string(ct.min(axis=0), precision=2))
    print('median:', np.array2string(np.median(ct, axis=0), precision=2), ' count < 1e-6:', (ct < 1e-6).sum(0))
    np.save('cb_ej.npy', np.column_stack([j, ct]))
