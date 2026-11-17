"""Probe 25: a word in Wave: Down (textWave1), PowerPoint vs two models.
  shear  : each point keeps its x and is lifted by the guide, x^3 - x shaped (guide traced by
           its Bezier parameter, which is linear in x here);
  arclen : the guide traced at constant speed, s = k*u, k fitted (PowerPoint's fill factor).
Usage: py probe_wave_overlay.py [TEXT] [PRESET] [WxH] [FONT]"""
import sys
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import minimize_scalar
import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
from warplab import *
text = sys.argv[1] if len(sys.argv) > 1 else "WAVES"; pr = sys.argv[2] if len(sys.argv) > 2 else "textWave1"
BOX = (100, 100) + tuple(float(x) for x in (sys.argv[3].split("x") if len(sys.argv) > 3 else ("504", "144")))
lab = Lab(visible=True)
try:
    FONT = sys.argv[4] if len(sys.argv) > 4 else "Arial"
    tb = lab.textbox(text, font=FONT, size=72, box=BOX); tb.TextFrame2.WarpFormat = WARP_ID[pr]
    flat, warped = lab.bake(tb, flat=True), lab.bake(tb)
finally:
    lab.close()
L, T, W, H = BOX; x0, y0, x1, y1 = inkbox(flat)
ps = paths(pr, W, H, None, L, T); gt, gb = Guide(ps[0]), Guide(ps[1])
WD = np.vstack([dense(s, 60) for s in warped]); tree = cKDTree(WD)
FP = [dense(s, 40) for s in flat]


def image(mode, k=1.0):
    out = []
    for P in FP:
        u = (P[:, 0] - x0) / (x1 - x0); v = (P[:, 1] - y0) / (y1 - y0)
        out.append(np.array([(1 - b) * gt.at(k * a, mode) + b * gb.at(k * a, mode) for a, b in zip(u, v)]))
    return out


def err(curves):
    M = np.vstack(curves); d1 = tree.query(M)[0]; d2 = cKDTree(M).query(WD)[0]
    return max(d1.max(), d2.max()), float(np.sqrt((d1 ** 2).mean()))


ks = minimize_scalar(lambda k: err(image("param", k))[1], bounds=(0.9, 1.05), method="bounded").x
shear = image("param", ks)
k = minimize_scalar(lambda k: err(image("arclen", k))[1], bounds=(0.9, 1.05), method="bounded").x
arc = image("arclen", k)
e_s, e_a = err(shear), err(arc)
print(f"shear (x^3 - x) model, k = {ks:.4f}: max {e_s[0]:.2f} pt, rms {e_s[1]:.2f} pt")
print(f"arc-length model, k = {k:.4f}: max {e_a[0]:.2f} pt, rms {e_a[1]:.2f} pt")
fig, axes = plt.subplots(1, 2, figsize=(13, 7)) if W < 1.6 * H else plt.subplots(2, 1, figsize=(12, 7.5))
for ax, curves, col, title in ((axes[0], shear, "#1f6fd1", f"shear model (x³ − x lift, k = {ks:.3f}):  max {e_s[0]:.1f} pt, rms {e_s[1]:.2f} pt"),
                              (axes[1], arc, "#d62728", f"arc-length model (k = {k:.3f}):  max {e_a[0]:.1f} pt, rms {e_a[1]:.2f} pt")):
    for s in warped: D = dense(s, 60); ax.plot(D[:, 0], D[:, 1], color="black", lw=2.2, alpha=0.55)
    for C in curves: ax.plot(C[:, 0], C[:, 1], color=col, lw=1.0)
    for g in (gt, gb):
        G = np.array([g.at(s, "param") for s in np.linspace(0, 1, 200)]); ax.plot(G[:, 0], G[:, 1], ":", color="gray", lw=0.8)
    ax.set_aspect("equal"); ax.invert_yaxis(); ax.set_title(title, fontsize=11); ax.set_xticks([]); ax.set_yticks([])
fig.suptitle(f"“{text}” in Wave: Down — grey: PowerPoint, colour: model, dotted: guides", fontsize=12)
fig.tight_layout(); fn = f"wave_overlay_{text if text.isascii() else 'U%04X' % ord(text[0])}_{int(W)}x{int(H)}.png"; fig.savefig(fn, dpi=110)
print("saved", fn)
