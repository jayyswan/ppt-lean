"""Probe 27: the 'squashed cubic' model for Wave: Down, x = 100 + 288u,
y = 136 + 216v - 90*lam*(s^3 - c*s), s = 2u - 1 (shear by a squashed x^3 - c x), with lam
calibrated on a black square and c = 0.95; compared with the arc-length model on other shapes.
Usage: py probe_friend_model.py"""
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import minimize
from warplab import *
BOX = (100, 100, 288, 288)
cases = [("■", "Segoe UI Symbol"), ("●", "Segoe UI Symbol"), ("WAVE", "Arial")]
data = {}
lab = Lab(visible=True)
try:
    for text, font in cases:
        tb = lab.textbox(text, font=font, size=72, box=BOX); tb.TextFrame2.WarpFormat = WARP_ID["textWave1"]
        data[text] = (lab.bake(tb, flat=True), lab.bake(tb)); tb.Delete()
finally:
    lab.close()
ps = paths("textWave1", 288, 288, None, 100, 100); gt, gb = Guide(ps[0]), Guide(ps[1])


def setup(text):
    flat, warped = data[text]; x0, y0, x1, y1 = inkbox(flat)
    P = np.vstack([dense(s, 60) for s in flat]); U = (P[:, 0] - x0) / (x1 - x0); V = (P[:, 1] - y0) / (y1 - y0)
    WD = np.vstack([dense(s, 80) for s in warped]); return U, V, WD, cKDTree(WD)


def score(M, WD, tree):
    d1 = tree.query(M)[0]; d2 = cKDTree(M).query(WD)[0]
    return float(np.sqrt((d1 ** 2).mean())), float(max(d1.max(), d2.max()))


def friend(U, V, lam, c=0.95):
    s = 2 * U - 1; return np.c_[100 + 288 * U, 136 + 216 * V - 90 * lam * (s ** 3 - c * s)]


def arclen(U, V, k):
    return np.array([(1 - v) * gt.at(k * u, "arclen") + v * gb.at(k * u, "arclen") for u, v in zip(U, V)])


U, V, WD, tr = setup("■")
lam = minimize(lambda p: score(friend(U, V, p[0]), WD, tr)[0], [0.6], method="Nelder-Mead").x[0]
print(f"calibrated on ■: lam = {lam:.3f}  (c = 0.95) -> ■ rms/max {score(friend(U, V, lam), WD, tr)}")
for text in ("●", "WAVE"):
    U, V, WD, tr = setup(text)
    fixed = score(friend(U, V, lam), WD, tr)
    best = minimize(lambda p: score(friend(U, V, p[0], p[1]), WD, tr)[0], [lam, 0.95], method="Nelder-Mead")
    k = minimize(lambda p: score(arclen(U, V, p[0]), WD, tr)[0], [0.976], method="Nelder-Mead").x[0]
    print(f"{text}: friend (lam from ■) rms/max {tuple(round(x, 2) for x in fixed)} | friend best lam {best.x[0]:.3f} c {best.x[1]:.3f} "
          f"rms/max {tuple(round(x, 2) for x in score(friend(U, V, *best.x), WD, tr))} | arc length k {k:.3f} rms/max "
          f"{tuple(round(x, 2) for x in score(arclen(U, V, k), WD, tr))}")
