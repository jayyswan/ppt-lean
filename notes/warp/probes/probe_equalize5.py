"""Probe 20: does a glyph's Equalize band depend on the rest of the row? Rows "HH": a small
glyph of fixed size next to a big glyph of varying size, both equalized; and single-glyph rows.
Usage: py probe_equalize5.py"""
import json
import numpy as np
from warplab import *
lab = Lab(visible=True)
out = []
try:
    def bands(sizes, font="Segoe UI Symbol"):
        tb = lab.textbox("H" * len(sizes), font=font, size=10, box=(100, 100, 3000, 400))
        tr = tb.TextFrame.TextRange
        for i, s in enumerate(sizes): tr.Characters(i + 1, 1).Font.Size = s
        tb.TextFrame2.TextRange.Font.Equalize = -1
        subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
        return [(round(dense(s, 30)[:, 1].min() - 100, 4), round(dense(s, 30)[:, 1].max() - 100, 4)) for s in subs]
    for small in (9, 13.5, 15):
        for big in [small] + [20, 21, 22, 23, 24, 25, 30, 40, 50, 60, 72, 73, 99, 100]:
            b = bands([small, big] if big != small else [small])
            r = dict(small=small, big=big, small_band=b[0], big_band=b[-1], small_H=round(b[0][1] - b[0][0], 3))
            print(r); out.append(r)
finally:
    lab.close()
json.dump(out, open("equalize5.json", "w"), indent=1)
