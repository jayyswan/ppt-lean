import numpy as np, glob, sys, mpmath as mp
sys.argv = ['x', '0', '0']
exec(open('D5_s11lines.py').read().split('sols = []')[0])
mp.mp.dps = 45
S = []
for f in sorted(glob.glob('s11_seed*.npy')):
    for z in np.load(f):
        if all(np.linalg.norm(z - w) > 1e-6 * (1 + np.linalg.norm(z)) for w in S): S.append(z)
Wm = [[mp.mpf(float(x)) for x in row] for row in W]
def FJ(zz):
    a, b = zz[:5], zz[5:]
    u = [Wm[0][i] + mp.fsum(a[k] * Wm[2 + k][i] for k in range(5)) for i in range(9)]
    v = [Wm[1][i] + mp.fsum(b[k] * Wm[2 + k][i] for k in range(5)) for i in range(9)]
    f = []; J = []
    for d in (3, 5):
        for j in range(d + 1):
            c = mp.binomial(d, j)
            f.append(c * mp.fsum(u[i] ** (d - j) * v[i] ** j for i in range(9)))
            du = [(d - j) * u[i] ** (d - j - 1) * v[i] ** j if d > j else 0 for i in range(9)]
            dv = [j * u[i] ** (d - j) * v[i] ** (j - 1) if j > 0 else 0 for i in range(9)]
            J.append([c * mp.fsum(Wm[2 + k][i] * du[i] for i in range(9)) for k in range(5)] +
                     [c * mp.fsum(Wm[2 + k][i] * dv[i] for i in range(9)) for k in range(5)])
    return mp.matrix(f), mp.matrix(J)
ok = []; bad = 0
for z in S:
    zz = mp.matrix([mp.mpc(complex(c)) for c in z])
    good = False
    for it in range(12):
        f, J = FJ(zz)
        if mp.norm(f) < mp.mpf(10) ** -38:
            good = True; break
        zz = zz - mp.lu_solve(J, f)
    if not good:
        bad += 1; continue
    zr = np.array([complex(c) for c in zz])
    if np.linalg.norm(zr - z) < 1e-6 * (1 + np.linalg.norm(z)):
        ok.append(zr)
    else:
        bad += 1
print('refined to 1e-38:', len(ok), 'failed', bad, 'of', len(S), 'real', sum(1 for z in ok if abs(z.imag).max() < 1e-10))
