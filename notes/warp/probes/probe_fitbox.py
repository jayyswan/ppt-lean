"""Probe 9: which normalizing box does PowerPoint use? Fits x0, x1, y0, y1 (and optionally a
per-glyph shift) so that the exact warp of the unwarped outline matches the warped one.
Usage: py probe_fitbox.py TEXT PRESET ADJ W H"""
import sys
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import least_squares
from warplab import *
exec(open("probe_ctrlpts.py", encoding="utf-8").read().split("text, pr, adj")[0].split("from warplab import *")[1])
text, pr, adj, W, H = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5])
SZ = float(sys.argv[6]) if len(sys.argv) > 6 else 72
lab = Lab(visible=True)
try:
    tb = lab.textbox(text, size=SZ, box=(100, 100, W, H)); tb.TextFrame2.WarpFormat = WARP_ID[pr]
    flat = lab.bake(tb, flat=True)
    xml_edit_reopen(lab, set_warp_xml(pr, {"adj": adj})); tb = lab.s.Shapes(1)
    warped = lab.bake(tb)
finally:
    lab.close()
a = adj / 100000
WD = np.vstack([dense(s, 80) for s in warped]); T = cKDTree(WD)
flat = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
Ps = [np.vstack([dense(s, 60)]) for s in flat]
CP = np.array([q for sub in flat for c in sub for q in c[1:]]); print("control-point box", np.round([CP[:,0].min(), CP[:,1].min(), CP[:,0].max(), CP[:,1].max()], 3))
ink = inkbox(flat); print("size", SZ, "segments", sum(len(x) for x in flat), sum(len(x) for x in warped), "measured ink box", np.round(ink, 3), "per-glyph x ranges",
      [tuple(np.round([P[:, 0].min(), P[:, 0].max()], 2)) for P in Ps])
def model(q, shifts):
    x0, y0, x1, y1 = q
    out = []
    for P, s in zip(Ps, shifts):
        u = (P[:, 0] + s - x0) / (x1 - x0); v = (P[:, 1] - y0) / (y1 - y0)
        X, Y = lean_map(pr, a, W, H, u, v); out.append(np.c_[X + 100, Y + 100])
    return np.vstack(out)
def res(z, k):
    return T.query(model(z[:4], np.r_[0, z[4:4 + k]] if k else [0] * len(Ps)))[0]
r0 = res(np.r_[ink], 0); print(f'measured box: max {r0.max():.3f} rms {np.sqrt((r0**2).mean()):.3f}')
for k in (0,):
    if k == 0 and False: pass
    z0 = np.r_[ink, np.zeros(k)]
    r = least_squares(res, z0, args=(k,))
    print(f"free shifts={k}: max {np.abs(r.fun).max():.3f} rms {np.sqrt((r.fun**2).mean()):.3f}",
          "box", np.round(r.x[:4], 2), "shifts", np.round(r.x[4:], 2))

import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
fig, ax = plt.subplots(figsize=(9, 9 * H / W))
for sub in warped: D = dense(sub, 60); ax.plot(D[:, 0], D[:, 1], "k-", lw=1.2)
M = model(ink, [0] * len(Ps)); ax.plot(M[:, 0], M[:, 1], "r.", ms=0.8)
ax.plot([100, 100 + W, 100 + W, 100, 100], [100, 100, 100 + H, 100 + H, 100], "b-", lw=0.5)
ax.set_aspect("equal"); ax.invert_yaxis(); fig.savefig(f"fitbox_{int(W)}x{int(H)}.png", dpi=80)
