"""Probe 11: is a row laid out as  x_{i+1} - x_i = advance_i * size / unitsPerEm + spacing ?
Compares glyph offsets in PowerPoint's unwarped outline with the font file's metrics
(fontTools). Spacing and size are set by COM (observation); the values used are ones the UI
reaches (0.1 pt size grid, 0.1 pt spacing, presets).
Usage: py probe_layout.py"""
import numpy as np
from fontTools.ttLib import TTFont
from warplab import *
FONT = TTFont(r"C:\Windows\Fonts\seguisym.ttf")
upm = FONT["head"].unitsPerEm; cmap = FONT.getBestCmap(); hmtx = FONT["hmtx"]; glyf = FONT["glyf"]
def met(ch):
    g = cmap[ord(ch)]; gl = glyf[g]
    return hmtx[g][0], (gl.xMin, gl.yMin, gl.xMax, gl.yMax), hmtx[g][1]
for ch in "●◗◖":
    print(ch, "advance, bbox, lsb:", met(ch), "upm", upm)
lab = Lab(visible=True)
try:
    for text, size, spc in (("●●", 72, 0), ("●●", 72.3, 0), ("●●", 72, 3), ("●●", 72, -1.5), ("◗◖", 72, 0),
                            ("◗◖", 40.7, 6), ("●◗", 72, 0)):
        tb = lab.textbox(text, size=size, box=(100, 100, 400, 200))
        tb.TextFrame2.TextRange.Font.Spacing = spc
        flat = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min())
        xs = [dense(s, 40)[:, 0].min() for s in flat]
        adv0, bb0, lsb0 = met(text[0]); adv1, bb1, lsb1 = met(text[1])
        pred = (adv0 - bb0[0] + bb1[0]) * size / upm + spc   # left ink edge to left ink edge
        ys = [(dense(s, 40)[:, 1].min(), dense(s, 40)[:, 1].max()) for s in flat]
        h_pred = [(met(c)[1][3] - met(c)[1][1]) * size / upm for c in text]
        print(f"{text} size {size} spacing {spc}: dx ppt {xs[1]-xs[0]:.3f} pred {pred:.3f} | "
              f"heights ppt {[round(b-a,3) for a,b in ys]} pred {[round(h,3) for h in h_pred]}")
        tb.Delete()
finally:
    lab.close()
