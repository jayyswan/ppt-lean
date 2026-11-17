"""Probe 18: Equalize band height H as a function of stored size (and offset), from rows of
mixed-size glyphs sharing one baseline. Each glyph is equalized onto its own band, so
H = bottom - top per glyph.
Usage: py probe_equalize4.py FONT OFFSET"""
import sys, json
import numpy as np
from warplab import *
font = sys.argv[1]; off = float(sys.argv[2]); CH = sys.argv[3] if len(sys.argv) > 3 else "H"
SIZES = [round(x, 1) for x in list(np.arange(1, 30, 0.5)) + list(range(30, 101)) + [72.4, 72.3, 50.2, 50.4, 13.3, 13.4]]
if off: SIZES = [x for x in SIZES if x >= 3]
lab = Lab(visible=True)
out = []
try:
    for chunk in [SIZES[i:i + 30] for i in range(0, len(SIZES), 30)]:
        tb = lab.textbox(CH * len(chunk), font=font, size=10, box=(100, 100, 6000, 400))
        tr = tb.TextFrame.TextRange
        for i, s in enumerate(chunk):
            c = tr.Characters(i + 1, 1); c.Font.Size = s
            if off: c.Font.BaselineOffset = off
        tb.TextFrame2.TextRange.Font.Equalize = -1
        subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
        assert len(subs) == len(chunk), (len(subs), len(chunk))
        for s, sub in zip(chunk, subs):
            D = dense(sub, 30); out.append(dict(S=s, top=round(D[:, 1].min(), 4), bot=round(D[:, 1].max(), 4),
                                                H=round(D[:, 1].max() - D[:, 1].min(), 4)))
finally:
    lab.close()
json.dump(out, open(f"equalize4_{font.replace(' ', '')}_{off}" + ("" if CH == "H" else "_%04X" % ord(CH)) + ".json", "w"), indent=1)
for r in out: print(r["S"], r["H"], r["bot"])
