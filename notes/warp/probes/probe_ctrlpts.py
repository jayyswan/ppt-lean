"""Probe 8: does PowerPoint warp the glyph's Bezier control points, or the exact curve?
Compares the warped outline with (a) the exact image of the unwarped outline (dense points
mapped) and (b) the unwarped Beziers with their control points mapped.
Usage: py probe_ctrlpts.py TEXT PRESET ADJ W H"""
import sys
import numpy as np
from scipy.spatial import cKDTree
from warplab import *


def lean_map(preset, a, w, h, u, v):
    s = np.abs(2 * u - 1)
    if preset == "textTriangle":
        T = (u * w, a * h * s); B = (u * w, h + 0 * u)
    else:
        T = (u * w, 0 * u); B = (u * w, h - (1 - a) * h * s)
    return (1 - v) * T[0] + v * B[0], (1 - v) * T[1] + v * B[1]

text, pr, adj, W, H = sys.argv[1], sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5])
lab = Lab(visible=True)
try:
    tb = lab.textbox(text, box=(100, 100, W, H)); tb.TextFrame2.WarpFormat = WARP_ID[pr]
    flat = lab.bake(tb, flat=True)
    xml_edit_reopen(lab, set_warp_xml(pr, {"adj": adj})); tb = lab.s.Shapes(1)
    warped = lab.bake(tb)
finally:
    lab.close()
ink = inkbox(flat); x0, y0, x1, y1 = ink; a = adj / 100000
def F(p):
    u, v = (p[0] - x0) / (x1 - x0), (p[1] - y0) / (y1 - y0)
    X, Y = lean_map(pr, a, W, H, np.array(u), np.array(v)); return np.array([X + 100, Y + 100])
segs = lambda subs: sum(len([c for c in s if c[0] in "LCQ"]) for s in subs)
print("segments flat", segs(flat), "warped", segs(warped), "| contours", len(flat), len(warped))
WD = np.vstack([dense(s, 80) for s in warped]); T = cKDTree(WD)
exact = np.array([F(p) for s in flat for p in dense(s, 80)])
ctrl = [[(c[0],) + tuple(F(q) for q in c[1:]) for c in s] for s in flat]
cp = np.vstack([dense(s, 80) for s in ctrl])
for name, M in (("exact image", exact), ("control points mapped", cp)):
    d1 = T.query(M)[0]; d2 = cKDTree(M).query(WD)[0]
    print(f"{name:22s} max {max(d1.max(), d2.max()):.3f} pt  rms {np.sqrt((d1**2).mean()):.3f}")
