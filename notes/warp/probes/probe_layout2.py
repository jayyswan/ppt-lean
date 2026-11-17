"""Probe 12: size quantization of outlines, and per-step vs cumulative pen snapping.
Usage: py probe_layout2.py"""
from fontTools.ttLib import TTFont
from warplab import *
upm = 2048; ADV = 1764; BB = 52.137 / 72   # ● height per pt of size (Segoe UI Symbol)
lab = Lab(visible=True)
try:
    for size in (72.1, 72.2, 72.24, 72.25, 72.26, 72.4, 72.5, 72.6, 72.75, 72.76, 72.9):
        tb = lab.textbox("●", size=size, box=(100, 100, 400, 200))
        s = lab.bake(tb, flat=True); D = np.vstack([dense(x, 40) for x in s])
        print(f"set {size}: stored {tb.TextFrame2.TextRange.Font.Size}, outline size {np.ptp(D[:,1]) / BB:.3f}")
        tb.Delete()
    for size, spc in ((40.5, 0), (40.5, 0.3), (24, 0.1), (13, 0)):
        tb = lab.textbox("●●●●", size=size, box=(100, 100, 600, 200))
        tb.TextFrame2.TextRange.Font.Spacing = spc
        fl = sorted(lab.bake(tb, flat=True), key=lambda x: dense(x, 10)[:, 0].min())
        xs = np.array([dense(x, 40)[:, 0].min() for x in fl]); d = xs - xs[0]
        step = ADV * size / upm + spc
        per = np.array([round(step / 0.75) * 0.75 * k for k in range(4)])
        cum = np.array([round(step * k / 0.75) * 0.75 for k in range(4)])
        print(f"size {size} spc {spc}: step {step:.4f} | ppt {np.round(d,3)} | per-step {per} | cumulative {cum}"
              f" | abs left {xs[0]:.4f}")
        tb.Delete()
finally:
    lab.close()
