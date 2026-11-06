"""Probe 7: does `Pptc/TextBox.lean` (TextBox.outline) reproduce PowerPoint?

For each case, the Lean model is evaluated literally: idealized glyph pieces (circle, half
disc) fitted to the unwarped outline, the ink box of the whole row normalized to [0,1]^2, then
`WarpPreset.map` in closed form (Triangle: top (u w, a h |2u-1|), bottom (u w, h)). The result
is compared with the warped outline PowerPoint bakes. Handle values other than the default
are injected into the XML (observation only).
Usage: py probe_textbox_model.py"""
import json
import numpy as np
from scipy.spatial import cKDTree
from warplab import *


def lean_map(preset, a, w, h, u, v):
    s = np.abs(2 * u - 1)
    if preset == "textTriangle":
        T = (u * w, a * h * s); B = (u * w, h + 0 * u)
    elif preset == "textTriangleInverted":
        T = (u * w, 0 * u); B = (u * w, h - (1 - a) * h * s)
    else:
        raise ValueError(preset)
    return (1 - v) * T[0] + v * B[0], (1 - v) * T[1] + v * B[1]


def ideal_pieces(contour, kind):
    """Dense points of the idealized glyph fitted to one unwarped contour (slide coords)."""
    P = dense(contour, 40); x0, x1 = P[:, 0].min(), P[:, 0].max(); y0, y1 = P[:, 1].min(), P[:, 1].max()
    r = (y1 - y0) / 2; cy = (y0 + y1) / 2; th = np.linspace(-np.pi / 2, np.pi / 2, 800)
    seg = np.linspace(-1, 1, 400)
    if kind == "●":
        t = np.linspace(0, 2 * np.pi, 1600); cx = (x0 + x1) / 2
        return np.c_[cx + (x1 - x0) / 2 * np.cos(t), cy + r * np.sin(t)], (x1 - x0) / (2 * r)
    if kind == "◗":   # flat side left
        cx = x0; arc = np.c_[cx + r * np.cos(th), cy + r * np.sin(th)]
        return np.r_[arc, np.c_[cx + 0 * seg, cy + r * seg]], (x1 - x0) / r
    if kind == "◖":   # flat side right
        cx = x1; arc = np.c_[cx - r * np.cos(th), cy + r * np.sin(th)]
        return np.r_[arc, np.c_[cx + 0 * seg, cy + r * seg]], (x1 - x0) / r
    raise ValueError(kind)


CASES_ALL = [  # text, preset, adj (None = default), box (L, T, W, H), margins (None = zero)
    ("◗", "textTriangle", 100000, (100, 100, 288, 288), None),
    ("◗", "textTriangle", None, (100, 100, 288, 288), None),
    ("◖", "textTriangleInverted", 0, (100, 100, 288, 288), None),
    ("●●", "textTriangle", None, (100, 100, 288, 288), None),
    ("◗◖", "textTriangle", 100000, (100, 100, 432, 216), None),
    ("◗", "textTriangle", 100000, (100, 100, 288, 288), "default"),
]

out = []
import sys
CASES = [CASES_ALL[int(i)] for i in sys.argv[1:]] or CASES_ALL
for text, pr, adj, box, margins in CASES:
    lab = Lab(visible=True)
    try:
        tb = lab.textbox(text, box=box)
        if margins == "default":
            tf = tb.TextFrame2
            tf.MarginLeft, tf.MarginRight, tf.MarginTop, tf.MarginBottom = 7.2, 7.2, 3.6, 3.6
        tb.TextFrame2.WarpFormat = WARP_ID[pr]
        flat = lab.bake(tb, flat=True)
        if adj is not None:
            xml_edit_reopen(lab, set_warp_xml(pr, {"adj": adj}))
            tb = lab.s.Shapes(1)
        warped = lab.bake(tb)
        tf = tb.TextFrame2
        m = (tf.MarginLeft, tf.MarginTop, tf.MarginRight, tf.MarginBottom)
        L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height
    finally:
        lab.close()
    a = (adj if adj is not None else 50000) / 100000
    # one idealized glyph per character, matched to the unwarped contours left to right
    flat_sorted = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
    ideal, aspect = [], []
    for ch, c in zip(text, flat_sorted):
        pts, asp = ideal_pieces(c, ch); ideal.append(pts); aspect.append(round(float(asp), 4))
    I = np.vstack(ideal)
    x0, x1, y0, y1 = I[:, 0].min(), I[:, 0].max(), I[:, 1].min(), I[:, 1].max()
    U, V = (I[:, 0] - x0) / (x1 - x0), (I[:, 1] - y0) / (y1 - y0)
    for frame, (ox, oy, w, h) in {
        "outer box": (L, T, W, H),
        "inset box": (L + m[0], T + m[1], W - m[0] - m[2], H - m[1] - m[3]),
    }.items():
        X, Y = lean_map(pr, a, w, h, U, V)
        M = np.c_[X + ox, Y + oy]
        WD = np.vstack([dense(s, 80) for s in warped])
        d_model = cKDTree(WD).query(M)[0]          # model point -> nearest PowerPoint point
        d_ppt = cKDTree(M).query(WD)[0]            # PowerPoint point -> nearest model point
        r = dict(text=text, preset=pr, adj=adj, box=box, margins=m, frame=frame,
                 glyph_aspect=aspect, model_to_ppt_max=round(float(d_model.max()), 3),
                 ppt_to_model_max=round(float(d_ppt.max()), 3),
                 rms=round(float(np.sqrt((d_model ** 2).mean())), 3))
        k = np.argsort(d_model)[-5:]
        r["worst_uv"] = [(round(float(U[i]), 3), round(float(V[i]), 3), round(float(d_model[i]), 2)) for i in k]
        j = np.argsort(d_ppt)[-3:]
        r["worst_ppt_xy_rel"] = [(round(float((WD[i,0]-ox)/w), 3), round(float((WD[i,1]-oy)/h), 3), round(float(d_ppt[i]), 2)) for i in j]
        import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(9, 9 * h / w))
        for s in warped: D = dense(s, 60); ax.plot(D[:, 0], D[:, 1], "k-", lw=1.2)
        ax.plot(M[:, 0], M[:, 1], "r.", ms=0.8); ax.set_aspect("equal"); ax.invert_yaxis()
        fig.savefig(f"tbmodel_{len(out)}.png", dpi=80); plt.close(fig)
        print(r); out.append(r)
        if margins is None:
            break
json.dump(out, open("textbox_model.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
