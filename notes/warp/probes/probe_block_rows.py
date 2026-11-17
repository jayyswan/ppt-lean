"""Probe 31: a 'square' built from N touching full blocks (Lucida Sans Unicode, U+2588, one em
wide) in Wave: Down. Each block edge spans 1/N of u, so PowerPoint's one-cubic-per-segment
drawing should approach the exact arc-length image as N grows. Reports the deviation from the
exact image with PowerPoint's own fill k (fitted) and with k = 1 (idealized).
Usage: py probe_block_rows.py [WxH]"""
import sys
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import minimize_scalar
from warplab import *
W, H = map(float, (sys.argv[1] if len(sys.argv) > 1 else "360x360").split("x"))
ps = paths("textWave1", W, H, None, 100, 100); gt, gb = Guide(ps[0]), Guide(ps[1])
lab = Lab(visible=True)
try:
    for N in (1, 2, 4, 8, 16):
        tb = lab.textbox("█" * N, font="Lucida Sans Unicode", size=72, box=(100, 100, W, H))
        tb.TextFrame2.WarpFormat = WARP_ID["textWave1"]
        flat, warped = lab.bake(tb, flat=True), lab.bake(tb); tb.Delete()
        x0, y0, x1, y1 = inkbox(flat)
        P = np.vstack([dense(s, 80) for s in flat]); U = (P[:, 0] - x0) / (x1 - x0); V = (P[:, 1] - y0) / (y1 - y0)
        WD = np.vstack([dense(s, 120) for s in warped]); tree = cKDTree(WD)
        def err(k):
            M = np.array([(1 - v) * gt.at(k * u, "arclen") + v * gb.at(k * u, "arclen") for u, v in zip(U, V)])
            d1 = tree.query(M)[0]; d2 = cKDTree(M).query(WD)[0]; return float(np.sqrt((d1 ** 2).mean())), float(max(d1.max(), d2.max()))
        k = minimize_scalar(lambda k: err(k)[0], bounds=(0.95, 1.01), method="bounded").x
        e_k, e_1 = err(k), err(1.0)
        print(f"N={N:2d} blocks ({len(flat)} contours): vs exact with PowerPoint's fill k={k:.4f}: rms {e_k[0]:.3f} max {e_k[1]:.3f} pt"
              f" | vs idealized (k=1): rms {e_1[0]:.3f} max {e_1[1]:.3f} pt", flush=True)
finally:
    lab.close()
