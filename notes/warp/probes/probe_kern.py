"""Probe 19: does PowerPoint kern, and by what rule? Pair advance with Font2.Kerning off/on.
Usage: py probe_kern.py"""
import numpy as np
from warplab import *
lab = Lab(visible=True)
try:
    for font, text, S in (("Arial", "AV", 72), ("Arial", "AV", 11), ("Arial", "AV", 13), ("Segoe UI Symbol", "◗◖", 72),
                          ("Segoe UI Symbol", "●●", 72)):
        for kern in (None, 0, 12):
            tb = lab.textbox(text, font=font, size=S, box=(100, 100, 600, 300))
            f2 = tb.TextFrame2.TextRange.Font
            default = f2.Kerning
            if kern is not None: f2.Kerning = kern
            subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
            xs = [dense(s, 40)[:, 0].min() for s in subs]
            print(font, text, S, "kerning", "default=%s" % default if kern is None else kern, "ink lefts", np.round(xs, 3))
finally:
    lab.close()
