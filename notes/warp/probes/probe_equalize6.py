import sys
FONT = sys.argv[1] if len(sys.argv) > 1 else "Segoe UI Symbol"
"""Probe 21: single-size equalized rows, one per pixel size n (S = 0.75 n): band top T and
bottom B relative to the box top, plus the plain baseline. Usage: py probe_equalize6.py"""
import json
import numpy as np
from warplab import *
lab = Lab(visible=True)
out = []
try:
    for n in range(2, 134):
        S = 0.75 * n; r = dict(n=n)
        for eq in (False, True):
            tb = lab.textbox("H", font=FONT, size=S, box=(100, 100, 600, 300))
            if eq: tb.TextFrame2.TextRange.Font.Equalize = -1
            subs = lab.bake(tb, flat=True); tb.Delete()
            if not subs: r["eq" if eq else "plain"] = None; continue
            D = np.vstack([dense(s, 30) for s in subs])
            r["eq" if eq else "plain"] = (round((D[:, 1].min() - 100) / 0.75, 3), round((D[:, 1].max() - 100) / 0.75, 3))
        out.append(r); print(r)
finally:
    lab.close()
json.dump(out, open("equalize6.json" if FONT == "Segoe UI Symbol" else "equalize6_%s.json" % FONT.replace(" ", ""), "w"), indent=1)
