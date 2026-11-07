"""Probe 26: does PowerPoint warp a glyph by mapping Bezier control points? Each straight
edge is treated as a cubic with control points at 1/3 and 2/3; every control point is mapped
by a warp model (shear or arc length, fill factor k fitted), and the resulting Beziers are
compared with PowerPoint's warped outline.
Usage: py probe_wave_ctrl.py TEXT PRESET WxH [FONT]"""
import sys
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import minimize_scalar
from warplab import *
text, pr = sys.argv[1], sys.argv[2]; W, H = map(float, sys.argv[3].split("x")); font = sys.argv[4] if len(sys.argv) > 4 else "Segoe UI Symbol"
BOX = (100, 100, W, H)
lab = Lab(visible=True)
try:
    tb = lab.textbox(text, font=font, size=72, box=BOX); tb.TextFrame2.WarpFormat = WARP_ID[pr]
    flat, warped = lab.bake(tb, flat=True), lab.bake(tb)
finally:
    lab.close()
print("flat segments", [[c[0] for c in s] for s in flat][:2])
print("warped segments", [[c[0] for c in s] for s in warped][:2])
L, T, _, _ = BOX; x0, y0, x1, y1 = inkbox(flat)
ps = paths(pr, W, H, None, L, T); gt, gb = Guide(ps[0]), Guide(ps[1])
WD = np.vstack([dense(s, 80) for s in warped]); tree = cKDTree(WD)


def F(p, mode, k):
    u = (p[0] - x0) / (x1 - x0); v = (p[1] - y0) / (y1 - y0)
    return (1 - v) * gt.at(k * u, mode) + v * gb.at(k * u, mode)


def cubics(sub):  # lines -> cubics with control points at thirds; quads -> cubics
    out, cur = [], None
    for c in sub:
        if c[0] == "M": cur = c[1]; out.append(("M", cur))
        elif c[0] == "L": out.append(("C", cur + (c[1] - cur) / 3, cur + 2 * (c[1] - cur) / 3, c[1])); cur = c[1]
        elif c[0] == "Q": out.append(("C", cur + 2 * (c[1] - cur) / 3, c[2] + 2 * (c[1] - c[2]) / 3, c[2])); cur = c[2]
        elif c[0] == "C": out.append(c); cur = c[3]
        else: out.append(c)
    return out


def ctrl_model(mode, k):
    return [[(c[0],) + tuple(F(q, mode, k) for q in c[1:]) for c in cubics(s)] for s in flat]


def exact_model(mode, k):
    return [np.array([F(p, mode, k) for p in dense(s, 60)]) for s in flat]


def err_curves(curves):
    M = np.vstack(curves); d1 = tree.query(M)[0]; d2 = cKDTree(M).query(WD)[0]
    return max(d1.max(), d2.max()), float(np.sqrt((d1 ** 2).mean()))


for name, mk in (("exact image", lambda m, k: exact_model(m, k)),
                 ("control points", lambda m, k: [dense(s, 80) for s in ctrl_model(m, k)])):
    for mode, lab_ in (("param", "shear"), ("arclen", "arc length")):
        k = minimize_scalar(lambda k: err_curves(mk(mode, k))[1], bounds=(0.9, 1.05), method="bounded").x
        e = err_curves(mk(mode, k))
        print(f"{name:15s} {lab_:10s} k={k:.4f}: max {e[0]:.3f} pt, rms {e[1]:.3f} pt")
