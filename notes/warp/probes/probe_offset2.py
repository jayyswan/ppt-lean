"""Probe 16: absolute baseline positions of offset glyphs, to find what is snapped.
One row: a plain ● then N ● each with its own baseline offset (UI-reachable values: even %
and -25 %). Reports, per glyph, the baseline y relative to the box top.
Usage: py probe_offset2.py SIZE [TOP]"""
import sys, json
import numpy as np
from warplab import *
UPM, YMIN, YMAX = 2048, -25, 1458
S = float(sys.argv[1]); TOP = float(sys.argv[2]) if len(sys.argv) > 2 else 100
OFFS = [round(x, 2) for x in np.arange(-1.0, 1.0001, 0.02) if abs(x) > 1e-9] + [-0.25]
lab = Lab(visible=True)
try:
    out = []
    for chunk in [OFFS[i:i + 25] for i in range(0, len(OFFS), 25)]:
        tb = lab.textbox("●" * (len(chunk) + 1), size=S, box=(100, TOP, 3000, 300))
        tr = tb.TextFrame.TextRange
        for i, o in enumerate(chunk): tr.Characters(i + 2, 1).Font.BaselineOffset = o
        subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
        bx = [(dense(s, 60)[:, 1].min(), dense(s, 60)[:, 1].max()) for s in subs]
        size = lambda b: (b[1] - b[0]) / ((YMAX - YMIN) / UPM)
        base = lambda b: b[1] + YMIN * size(b) / UPM - TOP
        b0 = base(bx[0])
        for o, b in zip(chunk, bx[1:]):
            out.append(dict(off=o, base0=round(b0, 4), base=round(base(b), 4), shift=round(b0 - base(b), 4),
                            raw=round(o * S, 4), drawn=round(size(b), 3)))
    for r in out: print(r)
    json.dump(out, open(f"offset2_{S}_{TOP}.json", "w"), indent=1)
finally:
    lab.close()
