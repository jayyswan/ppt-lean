"""Probe 28: exact Wave: Down data from the warped square, per box size: t1 (guide parameter
where u = 1 lands, from the right edge's x), and the bottom-edge cubic's handle ratios
c0, c3 (handle = c * guide derivative). Output wave_edges.json.
Usage: py probe_wave_edges.py"""
import json
import numpy as np
from warplab import *
BOXES = [(288, 288), (288, 432), (504, 144), (144, 144), (576, 288), (216, 288), (360, 360), (432, 432),
         (288, 144), (288, 216), (288, 360), (720, 288), (144, 288), (576, 576), (216, 216), (504, 288)]
out = []
lab = Lab(visible=True)
try:
    for W, H in BOXES:
        tb = lab.textbox("■", size=72, box=(100, 100, W, H)); tb.TextFrame2.WarpFormat = WARP_ID["textWave1"]
        warped = lab.bake(tb); tb.Delete()
        y1 = H * 0.125; dy2 = y1 * 10 / 3
        dB = lambda t: np.array([W, 3 * dy2 * ((1 - 2 * t) * (2 * t - 1) + 2 * t * (1 - t))])
        segs, cur = [], None
        for c in warped[0]:
            if c[0] == "M": cur = c[1]
            elif c[0] in "CL": segs.append((cur, c)); cur = c[-1]
        xmax = max(p[0] for p, c in segs); t1 = (xmax - 100) / W
        # bottom edge: a cubic whose start is the bottom-right corner (x = xmax, larger y) and ends at x = 100
        cands = [(p, c) for p, c in segs if c[0] == "C" and abs(p[0] - xmax) < 1e-3 and abs(c[3][0] - 100) < 1e-3]
        r = dict(W=W, H=H, t1=round(t1, 6), nseg=len(segs))
        if cands:
            p, c = max(cands, key=lambda pc: pc[0][1])
            h0 = c[1] - p; h3 = c[3] - c[2]
            r["c0"] = round(float(np.dot(h0, -dB(t1)) / np.dot(dB(t1), dB(t1))), 5)
            r["c3"] = round(float(np.dot(h3, -dB(0)) / np.dot(dB(0), dB(0))), 5)
            r["perp0"] = round(float(np.cross(h0, dB(t1)) / np.linalg.norm(dB(t1))), 4)
        print(r, flush=True); out.append(r)
finally:
    lab.close(); json.dump(out, open("wave_edges.json", "w"), indent=1)
