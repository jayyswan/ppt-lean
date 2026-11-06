"""Probe 17: the Equalize Character Height band, across fonts and sizes, with and without
baseline offset. Text "H" (flat bottom on the baseline). Reports, relative to the box top:
the plain baseline, and the equalized ink top/bottom.
Usage: py probe_equalize3.py"""
import json
import numpy as np
from warplab import *
FONTS = ["Segoe UI Symbol", "Arial", "Yu Gothic", "Times New Roman", "Calibri", "Cambria"]
SIZES = [9, 13, 20, 31, 50, 72, 100]
lab = Lab(visible=True)
out = []
try:
    for font in FONTS:
        for S in SIZES:
            r = dict(font=font, S=S)
            for name, eq, off in (("plain", False, 0), ("eq", True, 0), ("eq+30", True, 0.3), ("eq-25", True, -0.25),
                                  ("+30", False, 0.3), ("-25", False, -0.25)):
                tb = lab.textbox("H", font=font, size=S, box=(100, 100, 600, 300))
                if eq: tb.TextFrame2.TextRange.Font.Equalize = -1
                if off: tb.TextFrame.TextRange.Font.BaselineOffset = off
                D = np.vstack([dense(s, 40) for s in lab.bake(tb, flat=True)]); tb.Delete()
                r[name] = (round(D[:, 1].min() - 100, 4), round(D[:, 1].max() - 100, 4))
            print(r); out.append(r)
finally:
    lab.close()
json.dump(out, open("equalize3.json", "w"), indent=1)
