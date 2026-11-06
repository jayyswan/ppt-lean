"""Probe 15: exact behaviour of baseline offset (superscript/subscript).
Row "●●●" with an offset on the middle glyph only. Reports the middle glyph's drawn size
(from its ink height), its baseline shift, and the advance it gives the third glyph.
Offsets are those the UI reaches: even percentages (spinner) and the presets 30 %, -25 %.
Usage: py probe_offset.py"""
import numpy as np
from warplab import *
UPM, ADV, YMIN, YMAX, LSB = 2048, 1764, -25, 1458, 140


def glyph_boxes(subs):
    out = []
    for s in sorted(subs, key=lambda s: dense(s, 10)[:, 0].min()):
        D = dense(s, 60); out.append((D[:, 0].min(), D[:, 1].min(), D[:, 0].max(), D[:, 1].max()))
    return out


lab = Lab(visible=True)
rows = []
try:
    for S in (72, 72.4, 13, 20, 25, 31, 50, 9):
        for off in (0.02, 0.04, 0.3, -0.25, -0.02, 0.5, 1.0):
            tb = lab.textbox("●●●", size=S, box=(100, 100, 600, 300))
            tb.TextFrame.TextRange.Characters(2, 1).Font.BaselineOffset = off
            b = glyph_boxes(lab.bake(tb, flat=True)); tb.Delete()
            s0 = (b[0][3] - b[0][1]) / ((YMAX - YMIN) / UPM)        # drawn size of plain glyph
            s1 = (b[1][3] - b[1][1]) / ((YMAX - YMIN) / UPM)        # drawn size of offset glyph
            base0 = b[0][3] + YMIN * s0 / UPM                       # baseline y of plain glyph
            base1 = b[1][3] + YMIN * s1 / UPM                       # baseline y of offset glyph
            pen0 = b[0][0] - LSB * s0 / UPM; pen1 = b[1][0] - LSB * s1 / UPM; pen2 = b[2][0] - LSB * s0 / UPM
            r = dict(S=S, off=off, drawn_plain=round(s0, 3), drawn_off=round(s1, 3),
                     ratio=round(s1 / s0, 4), shift=round(base0 - base1, 3), adv_plain=round(pen1 - pen0, 3),
                     adv_off=round(pen2 - pen1, 3))
            print(r); rows.append(r)
finally:
    lab.close()
import json; json.dump(rows, open("offset.json", "w"), indent=1)
