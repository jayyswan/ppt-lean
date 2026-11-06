"""Probe 3: sweep all COM-settable presets with one test string. For each preset and each
pair of consecutive guide paths, fit the arc-length ruled model with a free fill factor k
(s = k u) and report corner error and interior-edge error (contours smaller than half the
ink box, so PowerPoint's coarse subdivision of long edges does not dominate).
Usage: py probe_sweep.py [text] [box_w box_h]"""
import sys, json
from warplab import *
from scipy.spatial import cKDTree
from scipy.optimize import minimize_scalar
text = sys.argv[1] if len(sys.argv) > 1 else "▦"
W, H = (float(sys.argv[2]), float(sys.argv[3])) if len(sys.argv) > 3 else (288.0, 288.0)
BOX = (100, 100, W, H)

def scored(pr, flat, warped, ink, pair, mode, k):
    ps = paths(pr, W, H, None, *BOX[:2])
    gt, gb = Guide(ps[pair[0]]), Guide(ps[pair[1]])
    x0, y0, x1, y1 = ink
    F = lambda p: warp_point(gt, gb, k * (p[0] - x0) / (x1 - x0), (p[1] - y0) / (y1 - y0), mode)
    WN = np.vstack([nodes(s) for s in warped])
    C = np.vstack([corners(s) for s in flat if len(corners(s))])
    ce = cKDTree(WN).query(np.array([F(c) for c in C]))[0]
    small = [s for s in flat if np.ptp(nodes(s)[:, 0]) < .5 * (x1 - x0)]
    WD = np.vstack([dense(s, 60) for s in warped])
    ee = (cKDTree(WD).query(np.array([F(p) for p in np.vstack([dense(s, 20) for s in small])]))[0]
          if small else np.array([np.nan]))
    return ce.max(), ee.max()

lab = Lab(); out = {}
try:
    tb = lab.textbox(text, box=BOX)
    flat = lab.bake(tb, flat=True); ink = inkbox(flat)
    for pr in WARP_ID:
        warped = lab.bake(tb, warp=pr)
        n = len(paths(pr, W, H))
        best = None
        for pair in [(i, i + 1) for i in range(0, n - 1)]:
            for mode in ("param", "arclen"):
                if mode == "param":
                    k = 1.0
                else:
                    k = minimize_scalar(lambda k: scored(pr, flat, warped, ink, pair, mode, k)[0],
                                        bounds=(0.9, 1.1), method="bounded").x
                c, e = scored(pr, flat, warped, ink, pair, mode, k)
                rec = dict(pair=pair, mode=mode, k=round(k, 5), corner=round(c, 3), edge=round(float(e), 3))
                out.setdefault(pr, []).append(rec)
                if best is None or c < best["corner"]: best = rec
        par = [r for r in out[pr] if r["mode"] == "param" and r["pair"] == best["pair"]][0]
        print(f"{pr:27s} paths={n} best pair={best['pair']} {best['mode']:6s} k={best['k']:.4f} "
              f"corner={best['corner']:7.3f} edge={best['edge']:7.3f} | param corner={par['corner']:7.3f}", flush=True)
finally:
    lab.close()
json.dump(out, open(f"sweep_{ord(text[0]):04X}_{int(W)}x{int(H)}.json", "w"), indent=1)
