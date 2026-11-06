"""Probe 14: Equalize Character Height in detail: the band (font, size, mixed sizes), baseline
offset (superscript/subscript), and whether a warp sees the equalized outline.
Usage: py probe_equalize2.py"""
import numpy as np
from scipy.spatial import cKDTree
from warplab import *


def bake_text(lab, text, font="Segoe UI Symbol", size=72, eq=False, sizes=None, base=None, warp=None):
    tb = lab.textbox(text, font=font, size=size, box=(100, 100, 500, 300))
    tr = tb.TextFrame.TextRange
    if eq: tb.TextFrame2.TextRange.Font.Equalize = -1
    if sizes:
        for i, s in enumerate(sizes): tr.Characters(i + 1, 1).Font.Size = s
    if base is not None: tr.Characters(len(text), 1).Font.BaselineOffset = base
    if warp: tb.TextFrame2.WarpFormat = WARP_ID[warp]
    subs = lab.bake(tb, flat=warp is None) if warp is None else (lab.bake(tb, flat=True), lab.bake(tb))
    tb.Delete(); return subs


def boxes(subs):
    out = []
    for s in sorted(subs, key=lambda s: dense(s, 10)[:, 0].min()):
        D = dense(s, 40); out.append(np.round([D[:, 0].min(), D[:, 1].min(), D[:, 0].max(), D[:, 1].max()], 3).tolist())
    return out


lab = Lab(visible=True)
try:
    print("-- band vs font and size")
    for font, size in (("Segoe UI Symbol", 72), ("Segoe UI Symbol", 36), ("Arial", 72), ("Yu Gothic", 72)):
        b = boxes(bake_text(lab, "●", font=font, size=size, eq=True))
        print(f"{font} {size}: box {b[0]}  band height {b[0][3] - b[0][1]:.3f}  (/size {(b[0][3]-b[0][1])/size:.5f})")
    print("-- mixed sizes, equalized")
    print("●● 72/36:", boxes(bake_text(lab, "●●", eq=True, sizes=(72, 36))))
    print("●● 72/36 plain:", boxes(bake_text(lab, "●●", sizes=(72, 36))))
    print("-- baseline offset on the last character")
    for base in (0, 0.3, -0.25, 0.5, 1.0):
        print(f"●● offset {base}:", boxes(bake_text(lab, "●●", base=base)))
    print("●● offset 0.3 equalized:", boxes(bake_text(lab, "●●", base=0.3, eq=True)))
    print("-- warp of an equalized row: model = Triangle map of the equalized flat outline")
    for text in ("●·", "·●·"):
        flat, warped = bake_text(lab, text, eq=True, warp="textTriangle")
        ink = inkbox(flat); x0, y0, x1, y1 = ink
        W, H = 500, 300; a = 0.5
        P = np.vstack([dense(s, 80) for s in flat]); u = (P[:, 0] - x0) / (x1 - x0); v = (P[:, 1] - y0) / (y1 - y0)
        X = u * W; Y = (1 - v) * a * H * np.abs(2 * u - 1) + v * H
        M = np.c_[X + 100, Y + 100]; WD = np.vstack([dense(s, 80) for s in warped])
        d = cKDTree(WD).query(M)[0]
        print(f"{text}: flat boxes {boxes(flat)} | model vs ppt max {d.max():.3f} rms {np.sqrt((d**2).mean()):.3f}")
finally:
    lab.close()
