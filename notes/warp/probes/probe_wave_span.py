"""Probe 30: how a straight edge's warped handles depend on its span in u. Rows of n squares
in Wave: Down (288x288). For every horizontal source edge (top or bottom of a square) the
warped cubic's end tangents and handle lengths are compared with the exact arc-length warp:
ratio = handle / ((1/3) * dF/du * du_edge). Output wave_span.json.
Usage: py probe_wave_span.py"""
import json
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from warplab import *
W = H = 288.0; L0, T0 = 100.0, 100.0
dy2 = H * 0.125 * 10 / 3
Bp = lambda t: np.array([W, 3 * dy2 * ((1 - 2 * t) * (2 * t - 1) + 2 * t * (1 - t))])
sp = lambda t: float(np.hypot(*Bp(t)))
out = []
lab = Lab(visible=True)
try:
    for n in (1, 2, 3, 4):
        tb = lab.textbox("■" * n, size=72, box=(L0, T0, W, H)); tb.TextFrame2.WarpFormat = WARP_ID["textWave1"]
        flat, warped = lab.bake(tb, flat=True), lab.bake(tb); tb.Delete()
        x0, y0, x1, y1 = inkbox(flat)
        # fill: from the rightmost warped x
        xmax = max(max(p[0] for c in s for p in c[1:] if len(c) > 1) for s in warped); t1 = (xmax - L0) / W
        Lest = quad(sp, 0, t1)[0]
        tu = lambda u: brentq(lambda t: quad(sp, 0, t)[0] - u * Lest, 0, 1)
        for s in warped:
            cur = None
            for c in s:
                if c[0] == "M": cur = c[1]; continue
                if c[0] == "C":
                    p0, p1, p2, p3 = cur, c[1], c[2], c[3]
                    if abs(p3[0] - p0[0]) > 5:   # a horizontal source edge (not a vertical side)
                        ua, ub = (p0[0] - L0) / W, (p3[0] - L0) / W       # guide params at ends (x = W t)
                        uu = lambda t: quad(sp, 0, t)[0] / Lest          # back to u
                        du = uu(ub) - uu(ua)
                        exact0 = (1 / 3) * du * Lest / sp(ua) * sp(ua)   # handle length of the exact Hermite at end a
                        r = dict(n=n, u_a=round(uu(ua), 4), u_b=round(uu(ub), 4), du=round(abs(du), 4),
                                 len_a=round(float(np.linalg.norm(p1 - p0)), 4), len_b=round(float(np.linalg.norm(p3 - p2)), 4),
                                 exact=round(abs(du) * Lest / 3, 4))
                        r["ratio_a"] = round(r["len_a"] / r["exact"], 4); r["ratio_b"] = round(r["len_b"] / r["exact"], 4)
                        out.append(r); print(r, flush=True)
                cur = c[-1] if c[0] != "Z" else cur
finally:
    lab.close(); json.dump(out, open("wave_span.json", "w"), indent=1)
