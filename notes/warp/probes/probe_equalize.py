"""Probe 13: what do Equalize Character Height and superscript/subscript do to glyph outlines?
For each text, bakes the unwarped outline with the effect off and on, and reports each
contour's box and the best affine map between the two versions (residual = how far from an
affine image). Effects are set by COM (observation); in the UI they are Font dialog
checkboxes.
Usage: py probe_equalize.py [FONT]"""
import sys
import numpy as np
from warplab import *
font = sys.argv[1] if len(sys.argv) > 1 else "Segoe UI Symbol"
TEXTS = ["●", "●●", "●·", "◗◖", "●▪", "·", "A", "Ag", "●A"]


def contours(lab, text, eq=False, base=None, size=72):
    tb = lab.textbox(text, font=font, size=size, box=(100, 100, 500, 300))
    f = tb.TextFrame2.TextRange.Font
    if eq: f.Equalize = -1
    if base is not None:
        tb.TextFrame2.TextRange.Characters(len(text), 1).Font.BaselineOffset = base
    subs = lab.bake(tb, flat=True)
    tb.Delete()
    return sorted(subs, key=lambda s: (round(dense(s, 10)[:, 0].min(), 1), dense(s, 10)[:, 1].min()))


def box(s):
    D = dense(s, 40); return np.round([D[:, 0].min(), D[:, 1].min(), D[:, 0].max(), D[:, 1].max()], 3)


def affine_fit(a, b):
    A, B = nodes(a), nodes(b)
    if len(A) != len(B): return None
    X = np.c_[A, np.ones(len(A))]; M, *_ = np.linalg.lstsq(X, B, rcond=None)
    return np.round(M.T, 4), round(float(np.abs(X @ M - B).max()), 4)


lab = Lab(visible=True)
try:
    for text in TEXTS:
        off, on = contours(lab, text), contours(lab, text, eq=True)
        print(f"== {text!r}: contours {len(off)} -> {len(on)}")
        for a, b in zip(off, on):
            r = affine_fit(a, b)
            print("   off", box(a), "on", box(b), "| affine", None if r is None else (r[0].tolist(), "resid", r[1]))
    for text, base in (("●●", 0.3), ("●●", -0.25), ("●●", 0.5)):
        off, on = contours(lab, text), contours(lab, text, base=base)
        print(f"== {text!r} last char baseline offset {base}")
        for a, b in zip(off, on):
            print("   off", box(a), "on", box(b))
finally:
    lab.close()
