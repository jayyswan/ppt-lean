"""Probe 32: the Lean `WarpPreset.map` of every modelled preset, at every UI-reachable handle
setting, against PowerPoint's own warped outline.

The guides below are written from the Lean definitions in `Pptc/TextBox.lean` (closed forms,
not the spec parser in warplab), traced by arc length numerically. The text "◗●◖" (Segoe UI
Symbol) is idealized glyph by glyph (true circle / half discs), normalized to its ink box and
sent through the map. Handle values other than the default are written into the XML; probe 4
(`probe_handle.py`) showed the UI drags that store exactly these values.
Usage: py probe_presets_model.py [preset ...]    -> presets_model.json, presets_model_*.png"""
import sys, json, math
import numpy as np
from scipy.spatial import cKDTree
from warplab import *

PI = math.pi


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


def seg(p, q):
    p, q = np.array(p, float), np.array(q, float)
    return lambda t: (1 - t)[:, None] * p + t[:, None] * q


def poly(pts):
    pts = [np.array(p, float) for p in pts]; n = len(pts) - 1
    def g(t):
        i = np.minimum((t * n).astype(int), n - 1); s = t * n - i
        P0 = np.array([pts[j] for j in i]); P1 = np.array([pts[j + 1] for j in i])
        return (1 - s)[:, None] * P0 + s[:, None] * P1
    return g


def ell_par(c, wR, hR, ph0, dph):
    return lambda t: np.c_[c[0] + wR * np.cos(ph0 + t * dph), c[1] + hR * np.sin(ph0 + t * dph)]


def ell_vis(c, wR, hR, th0, dth):
    def g(t):
        th = th0 + t * dth
        r = wR * hR / np.sqrt((hR * np.cos(th)) ** 2 + (wR * np.sin(th)) ** 2)
        return np.c_[c[0] + r * np.cos(th), c[1] + r * np.sin(th)]
    return g


def bez(p1, p2, p3, p4):
    P = [np.array(p, float) for p in (p1, p2, p3, p4)]
    return lambda t: ((1 - t) ** 3)[:, None] * P[0] + (3 * (1 - t) ** 2 * t)[:, None] * P[1] + \
        (3 * (1 - t) * t ** 2)[:, None] * P[2] + (t ** 3)[:, None] * P[3]


def trace(g, n=40001):
    """arcTrace: u -> g(least t with arclength(0, t) >= u * total)."""
    t = np.linspace(0, 1, n); P = g(t)
    cum = np.concatenate([[0], np.cumsum(np.hypot(*np.diff(P, axis=0).T))])
    if cum[-1] == 0: return lambda u: np.repeat(P[:1], len(u), 0)
    return lambda u: g(np.interp(u * cum[-1], cum, t))


def closed(f):  # a guide already traced at constant speed
    return lambda u: np.array([f(x) for x in u])


DEG = 60000 * 180 / PI  # DrawingML angle units per radian


def guides(k, a, b, w, h):
    """(top, bottom) as functions of u (arrays). Mirrors WarpPreset.map in Pptc/TextBox.lean."""
    c = (w / 2, h / 2)
    if k == "square":
        return (seg((max(0, w - 2 * a * w), 0), (min(w, 2 * (1 - a) * w), 0)),
                seg((max(0, (2 * a - 1) * w), h), (min(w, 2 * a * w), h)))
    if k == "stop":
        return (trace(poly([(0, a * h), (w / 3, 0), (2 * w / 3, 0), (w, a * h)])),
                trace(poly([(0, h - a * h), (w / 3, h), (2 * w / 3, h), (w, h - a * h)])))
    if k == "triangleUp":
        return closed(lambda u: (u * w, a * h * abs(2 * u - 1))), seg((0, h), (w, h))
    if k == "triangleDown":
        return seg((0, 0), (w, 0)), closed(lambda u: (u * w, h - (1 - a) * h * abs(2 * u - 1)))
    if k == "chevronUp":
        return (closed(lambda u: (u * w, a * h * abs(2 * u - 1))),
                closed(lambda u: (u * w, h - a * h * (1 - abs(2 * u - 1)))))
    if k == "chevronDown":
        return (closed(lambda u: (u * w, (1 - a) * h * (1 - abs(2 * u - 1)))),
                closed(lambda u: (u * w, h - (1 - a) * h * abs(2 * u - 1))))
    if k == "fadeRight": return seg((0, 0), (w, a * h)), seg((0, h), (w, h - a * h))
    if k == "fadeLeft": return seg((0, a * h), (w, 0)), seg((0, h - a * h), (w, h))
    if k == "fadeUp": return seg((a * w, 0), (w - a * w, 0)), seg((0, h), (w, h))
    if k == "fadeDown": return seg((0, 0), (w, 0)), seg((a * w, h), (w - a * w, h))
    if k == "slantUp": return seg((0, a * h), (w, 0)), seg((0, h), (w, h - a * h))
    if k == "slantDown": return seg((0, 0), (w, h - a * h)), seg((0, a * h), (w, h))
    if k == "cascadeUp": return seg((0, (1 - a) * h / 4), (w, 0)), seg((0, h), (w, a * h))
    if k == "cascadeDown": return seg((0, 0), (w, (1 - a) * h / 4)), seg((0, a * h), (w, h))
    if k == "warpUp":
        d = (1 - a) * h
        return (trace(ell_par((w / 2, d), w / 2, d, PI, PI)),
                trace(ell_par((w / 2, h), w / 2, d, PI, PI)))
    if k == "warpDown":
        d = a * h
        return (trace(ell_par((w / 2, 0), w / 2, d, PI, -PI)),
                trace(ell_par((w / 2, h - d), w / 2, d, PI, -PI)))
    if k in ("ringInside", "ringOutside"):
        r = a * h / 2; sw = (1 if k == "ringInside" else -1) * 21599999 / DEG
        return (trace(ell_vis((w / 2, r), w / 2, r, PI, sw)),
                trace(ell_vis((w / 2, h - r), w / 2, r, PI, sw)))
    if k in ("archWarped", "warpedButton"):
        return (trace(ell_par(c, w / 2, h / 2, PI, PI)),
                trace(ell_par(c, a * w / 2, a * h / 2, PI, PI)))
    if k == "archWarpedDown":
        return (trace(ell_par(c, a * w / 2, a * h / 2, PI, -PI)),
                trace(ell_par(c, w / 2, h / 2, PI, -PI)))
    if k == "warpedCircle":
        sw = 21599998 / DEG
        return trace(ell_vis(c, w / 2, h / 2, PI, sw)), trace(ell_vis(c, a * w / 2, a * h / 2, PI, sw))
    if k == "waveDown":
        y1 = a * h; d = 10 / 3 * y1; y4 = h - y1; sp = (1 - 2 * abs(b)) * w
        xt, xb = max(0, -2 * b * w), max(0, 2 * b * w)
        G = lambda x, y: trace(bez((x, y), (x + sp / 3, y - d), (x + 2 * sp / 3, y + d), (x + sp, y)))
        return G(xt, y1), G(xb, y4)
    raise KeyError(k)


# name -> (spec preset, handle-1 stops (min, default, max; None = unreachable), handle-2 stops)
PRESETS = {
    "square": ("textPlain", (30000, 50000, 70000)),
    "stop": ("textStop", (14286, 25000, 50000)),
    "triangleUp": ("textTriangle", (0, 50000, 100000)),
    "triangleDown": ("textTriangleInverted", (0, 50000, 100000)),
    "chevronUp": ("textChevron", (0, 25000, 50000)),
    "chevronDown": ("textChevronInverted", (50000, 75000, 100000)),
    "fadeRight": ("textFadeRight", (0, 33333, 49999)),
    "fadeLeft": ("textFadeLeft", (0, 33333, 49999)),
    "fadeUp": ("textFadeUp", (0, 33333, 49999)),
    "fadeDown": ("textFadeDown", (0, 33333, 49999)),
    "slantUp": ("textSlantUp", (0, 55555, 71431)),
    "slantDown": ("textSlantDown", (28569, 44445, 100000)),
    "cascadeUp": ("textCascadeUp", (28570, 44444, 100000)),
    "cascadeDown": ("textCascadeDown", (28570, 44444, 100000)),
    "warpUp": ("textCanUp", (66667, 85714, 100000)),
    "warpDown": ("textCanDown", (0, 14286, 33333)),
    "ringInside": ("textRingInside", (50000, 60000, 99000)),
    "ringOutside": ("textRingOutside", (50000, 60000, 99000)),
    "archWarped": ("textArchUpPour", (None, 50000, 99000)),
    "archWarpedDown": ("textArchDownPour", (None, 25000, 99000)),
    "warpedCircle": ("textCirclePour", (None, 50000, 99000)),
    "warpedButton": ("textButtonPour", (40000, 50000, 99000)),
    "waveDown": ("textWave1", (0, 12500, 20000), (-10000, 0, 10000)),
}
POLAR_DEFAULT_ANGLE = {"textArchUpPour": 10800000, "textArchDownPour": 0,
                       "textCirclePour": 10800000, "textButtonPour": 10800000}
TEXT = "◗●◖"


def cases(names):
    for k in names:
        spec, h1, *h2 = PRESETS[k]
        h2 = h2[0] if h2 else (None, 0, None)
        for s1, v1 in zip(("min", "default", "max"), h1):
            for s2, v2 in zip(("min", "default", "max"), h2):
                if v1 is None or v2 is None: continue
                if s1 != "default" and s2 != "default": continue  # one handle at a time
                yield k, spec, s1, v1, s2, v2


def stored_adj(spec, v1, v2):
    if spec in POLAR_DEFAULT_ANGLE:
        return {"adj1": POLAR_DEFAULT_ANGLE[spec], "adj2": v1}
    if spec == "textWave1":
        return {"adj1": v1, "adj2": v2}
    return {"adj": v1}


if __name__ == "__main__":
    names = sys.argv[1:] or list(PRESETS)
    boxes = [(100, 100, 288, 288), (100, 100, 360, 216)]
    out = []
    for k, spec, s1, v1, s2, v2 in cases(names):
        for box in boxes:
            if box != boxes[0] and (s1, s2) != ("default", "default"): continue
            lab = Lab(visible=True)
            try:
                tb = lab.textbox(TEXT, box=box)
                tb.TextFrame2.WarpFormat = WARP_ID[spec]
                flat = lab.bake(tb, flat=True)
                xml_edit_reopen(lab, set_warp_xml(spec, stored_adj(spec, v1, v2)))
                tb = lab.s.Shapes(1)
                warped = lab.bake(tb)
                L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height
            finally:
                lab.close()
            fs = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
            I = np.vstack([ideal_pieces(cn, ch)[0] for ch, cn in zip(TEXT, fs)])
            x0, x1, y0, y1 = I[:, 0].min(), I[:, 0].max(), I[:, 1].min(), I[:, 1].max()
            U, V = (I[:, 0] - x0) / (x1 - x0), (I[:, 1] - y0) / (y1 - y0)
            gt, gb = guides(k, v1 / 100000, v2 / 100000, W, H)
            M = (1 - V)[:, None] * gt(U) + V[:, None] * gb(U) + np.array([L, T])
            WD = np.vstack([dense(s, 80) for s in warped])
            d1 = cKDTree(WD).query(M)[0]; d2 = cKDTree(M).query(WD)[0]
            r = dict(preset=k, spec=spec, handle1=s1, handle2=s2, adj=stored_adj(spec, v1, v2),
                     box=box[2:], model_to_ppt_max=round(float(d1.max()), 3),
                     ppt_to_model_max=round(float(d2.max()), 3),
                     rms=round(float(np.sqrt((d1 ** 2).mean())), 3))
            print(r, flush=True); out.append(r)
            import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
            fig, ax = plt.subplots(figsize=(5, 5 * H / W))
            for s in warped: D = dense(s, 60); ax.plot(D[:, 0], D[:, 1], "k-", lw=1)
            ax.plot(M[:, 0], M[:, 1], "r.", ms=0.6); ax.set_aspect("equal"); ax.invert_yaxis()
            ax.set_title(f"{k} {s1}/{s2} {int(W)}x{int(H)}", fontsize=9)
            fig.savefig(f"presets_model_{k}_{s1}_{s2}_{int(W)}x{int(H)}.png", dpi=60); plt.close(fig)
            json.dump(out, open("presets_model.json" if len(names) > 3 else
                                f"presets_model_{'_'.join(names)}.json", "w"), indent=1)
