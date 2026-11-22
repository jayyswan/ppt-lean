"""Session 33. Real components of E_C (the cubic through the 9 points of a C_b^gen conic)
and how many of the 9 points lie on the oval when E_C(R) has two components.
Method: project from p0 = q_b (first b with two intervals when j > 1728; from a point
on the oval every residual pair is real, so that base point is skipped); real residual points exist where disc(phi) >= 0; each
interval of disc >= 0 on RP^1 is one real component (minus p0).  p0's component is the
interval containing its tangent direction.  Oval vs pseudoline: x is on the oval iff its
tangential T(x) lies on the other component.  Reads cb_good.npy, cb_lab.npy; needs grp.py
and cb_ej.py alongside.  Writes cb_comp.npy (j, ncomp, k_oval)."""
import numpy as np, sys
sys.argv = ['x', '1']
exec(open('cb_ej.py').read().split("\nif __name__ == '__main__'")[0])
from collections import Counter
def label_fn(cf, p0):
    A, B = np.linalg.svd(p0.reshape(1, 3))[2][1:]
    g0 = grad(cf, p0)
    ph = np.linspace(0, np.pi, 8000, endpoint=False)
    D = np.array([np.cos(ph), np.sin(ph)]).T @ np.array([A, B])
    E = np.array(M3)
    a1 = D @ g0; a3 = (np.prod(D[:, None, :] ** E[None], axis=2)) @ cf
    a2 = sum(cf[m] * E[m, j] * p0[j] * np.prod(D ** (E[m] - np.eye(3, dtype=int)[j]).clip(0), axis=1) for m in range(10) for j in range(3) if E[m, j])
    pos = (a2 ** 2 - 4 * a1 * a3) >= 0
    # intervals of pos on the circle
    if pos.all(): ivl = np.zeros(len(ph), int)
    else:
        sh = np.argmin(pos); ivl = -np.ones(len(ph), int); c = -1; prev = False
        for t in range(len(ph)):
            i = (sh + t) % len(ph)
            if pos[i] and not prev: c += 1
            if pos[i]: ivl[i] = c
            prev = pos[i]
    def lab(x):
        x = nz(x)
        if dist(x, p0) < 1e-7:
            t = np.cross(p0, g0)
        else:
            t = x - (x @ p0) * p0
        phi = np.arctan2(t @ B, t @ A) % np.pi
        i = int(round(phi / np.pi * len(ph))) % len(ph)
        if ivl[i] < 0:  # numerical edge: nearest positive
            for w in range(1, 200):
                for jj in (i - w, i + w):
                    if ivl[jj % len(ph)] >= 0: return ivl[jj % len(ph)]
        return ivl[i]
    return lab, ivl.max() + 1
if __name__ == '__main__':
    rng = np.random.default_rng(0)
    Qs = np.load('cb_good.npy'); labs = np.load('cb_lab.npy'); res = []; cnt = Counter()
    for Q, l in zip(Qs, labs):
        if l != 'gen': continue
        q = Q / np.linalg.norm(Q, axis=1)[:, None]
        cf = cubic_through(q)[0]; j = jinv(cf, q[0], rng).real
        for b0 in range(9):
            lab, nc = label_fn(cf, nz(q[b0]))
            if nc == 2 or j < 1728: break
        L = [lab(x) for x in q]
        if nc == 2:
            Tl = [lab(third(cf, nz(x), nz(x))) for x in q]
            oval = [L[i] for i in range(9) if Tl[i] != L[i]]
            ok = len(set(oval)) <= 1
            ovl = oval[0] if oval else None
            k = sum(1 for x in L if x == ovl) if ovl is not None else 0
            cnt[('2comp', 'k_oval', k, 'consistent' if ok else 'INCONSISTENT')] += 1
        else:
            k = -1; cnt[('ncomp', nc, 'j>1728' if j > 1728 else 'j<1728')] += 1
        if nc == 2: cnt[('2comp', 'j>1728' if j > 1728 else 'j<1728')] += 1
        res.append((j, nc, k))
    for kk, v in sorted(cnt.items(), key=str): print(kk, v)
    np.save('cb_comp.npy', np.array(res))
