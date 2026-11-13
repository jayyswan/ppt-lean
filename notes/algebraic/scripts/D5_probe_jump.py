import pickle, sys, numpy as np
exec(open('D5_probe.py').read().split('if __name__')[0])
allpts = pickle.load(open('jump_points.pkl', 'rb'))
for key, zs in sorted(allpts.items(), key=lambda kv: -len(kv[1])):
    for z in zs[:2]:
        A = np.array([1, 0, z[0], z[1]]); B = np.array([0, 1, z[2], z[3]])
        u0, v0 = pairing_line(A, B)
        res = probe(u0, v0, eps_list=(3e-2, 3e-3, 3e-4), nst=120)
        print("kernel", key[0], "J-dim<=", key[1], key[2][:2], "|", "  ".join(f"eps {e:.0e}: {n} good, ratio {b/e:.1f}" for e, n, b in res))
