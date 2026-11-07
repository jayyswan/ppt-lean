"""Probe 29: the map u -> t for Wave: Down, measured from a row of thin vertical bars. At
default handles x = W*t on the guide, so a vertical stem at ink fraction u lands at x = W*t(u).
Output wave_tmap_<W>x<H>.json: pairs (u, t) for every stem edge.
Usage: py probe_wave_tmap.py WxH"""
import sys, json
import numpy as np
from warplab import *
W, H = map(float, sys.argv[1].split("x"))
lab = Lab(visible=True)
try:
    tb = lab.textbox("|" * 24, font="Arial", size=40, box=(100, 100, W, H)); tb.TextFrame2.WarpFormat = WARP_ID["textWave1"]
    flat, warped = lab.bake(tb, flat=True), lab.bake(tb)
finally:
    lab.close()
x0, y0, x1, y1 = inkbox(flat)
def vedges(subs):  # x of vertical straight segments (lines or degenerate cubics with constant x)
    xs = []
    for s in subs:
        cur = start = None
        for c in s:
            if c[0] == "M": cur = start = c[1]; continue
            if c[0] == "Z":
                if abs(start[0] - cur[0]) < 1e-3 and abs(start[1] - cur[1]) > 1: xs.append(cur[0])
                continue
            if c[0] in "LC":
                end = c[-1]; pts = [cur] + list(c[1:])
                if max(abs(p[0] - cur[0]) for p in pts) < 1e-3 and abs(end[1] - cur[1]) > 1: xs.append(cur[0])
                cur = end
    return sorted(set(round(x, 4) for x in xs))
fx = vedges(flat); wx = vedges(warped)
print("flat stem edges", len(fx), "warped", len(wx))
pairs = [((a - x0) / (x1 - x0), (b - 100) / W) for a, b in zip(fx, wx)] if len(fx) == len(wx) else []
json.dump(dict(W=W, H=H, pairs=pairs, fx=fx, wx=wx), open(f"wave_tmap_{int(W)}x{int(H)}.json", "w"), indent=1)
print(pairs[:4], "...", pairs[-3:])
