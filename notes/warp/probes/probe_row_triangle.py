"""Probe 36 (probe 23 with the Lower Right Triangle): end-to-end check of Pptc/TextBox.lean's row model (sizes, spacing, superscript,
subscript, Equalize) against PowerPoint. Predictions come from `#eval` of the Lean definitions
(file given as argument: two lists of exact (x0, y0, x1, y1) boxes, plain then equalized).
Usage: py probe_row_triangle.py rowcheck_triangle_out.txt   (from RowCheckTriangle.lean)"""
import sys, re
from fractions import Fraction as F
import numpy as np
from warplab import *
txt = open(sys.argv[1]).read().split("]\n[")
def parse(t):
    nums = re.findall(r"(-?\d+)(?: / (\d+))?", t)
    v = [float(F(int(a), int(b) if b else 1)) for a, b in nums]
    return [v[i:i + 4] for i in range(0, len(v), 4)]
pred = {False: parse(txt[0]), True: parse(txt[1])}
ROW = [("◢", 72, 0, 0), ("●", 40.7, 0, 0.3), ("◢", 20, 3, -0.25), ("●", 13, 1.5, 0), ("◢", 100, 3, 0.02),
       ("●", 10, 0, 0), ("◢", 10.7, 0, 0)]
lab = Lab(visible=True)
try:
    for eq in (False, True):
        tb = lab.textbox("".join(c for c, *_ in ROW), size=10, box=(100, 100, 800, 400))
        tr = tb.TextFrame.TextRange; t2 = tb.TextFrame2.TextRange
        for i, (c, s, spc, off) in enumerate(ROW):
            ch = tr.Characters(i + 1, 1); ch.Font.Size = s; ch.Font.BaselineOffset = off
            t2.GetCharacters(i + 1, 1).Font.Spacing = spc
        if eq: t2.Font.Equalize = -1
        subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
        G = np.array([[dense(s, 60)[:, 0].min(), dense(s, 60)[:, 1].min(), dense(s, 60)[:, 0].max(), dense(s, 60)[:, 1].max()]
                      for s in subs])
        P = np.array(pred[eq])
        G[:, [0, 2]] -= 100; dy = G[0, 3] - P[0, 3]; G[:, [1, 3]] -= dy   # pen 0 = box left; baseline from glyph 0
        print("equalize" if eq else "plain", "| max error", round(float(np.abs(G - P).max()), 4), "pt")
        for p, g in zip(P, G): print("   pred", np.round(p, 3), "ppt", np.round(g, 3))
finally:
    lab.close()
