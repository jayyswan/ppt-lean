"""Probe 2: the law s(u) along the top guide. For each flat corner (u, v), find the guide
fraction s at which PowerPoint put it, assuming the ruled form (1-v) T(s) + v B(s); compare
s with u under arclength. Prints the fitted s/u ratio and residual."""
import sys
from warplab import *
from scipy.optimize import minimize_scalar
text = sys.argv[1]; presets = sys.argv[2:]
BOX = (100, 100, 288, 288)
lab = Lab()
try:
    tb = lab.textbox(text, box=BOX)
    flat = lab.bake(tb, flat=True); ink = inkbox(flat)
    x0, y0, x1, y1 = ink
    for pr in presets:
        warped = lab.bake(tb, warp=pr)
        WN = np.vstack([nodes(s) for s in warped])
        ps = paths(pr, 288, 288, None, 100, 100)
        gt, gb = Guide(ps[0]), Guide(ps[1])
        rows = []
        for C in [corners(s) for s in flat]:
            for c in C:
                u = (c[0] - x0) / (x1 - x0); v = (c[1] - y0) / (y1 - y0)
                # actual node: nearest warped node to the arclength prediction
                pred = warp_point(gt, gb, u, v, "arclen")
                w = WN[np.argmin(np.hypot(*(WN - pred).T))]
                f = lambda s: np.hypot(*((1 - v) * gt.at(s, "arclen") + v * gb.at(s, "arclen") - w))
                r = minimize_scalar(f, bounds=(max(0, u - .15), min(1, u + .15)), method="bounded")
                rows.append((u, v, r.x, r.fun))
        R = np.array(rows)
        k = np.linalg.lstsq(R[:, :1], R[:, 2], rcond=None)[0][0]
        print(f"{pr:24s} s/u slope={k:.5f}  resid(max)={np.abs(R[:,2]-k*R[:,0]).max():.4f} "
              f"fit-dist(max)={R[:,3].max():.3f}")
        for uu in (0.1, 0.5, 0.9):
            j = np.argmin(abs(R[:, 0] - uu)); print(f"     u={R[j,0]:.3f} v={R[j,1]:.3f} s={R[j,2]:.4f}")
finally:
    lab.close()
