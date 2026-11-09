"""Probe 40a: is the unwarped ink frame independent of the box aspect ratio?

The Lean model normalizes a fixed ink set `T.ink` by its own bounding box, so the
normalized coordinates `(u, v)` must not depend on the text box's width or height.
This probe bakes only the flat outline at several boxes and compares the normalized
outline point by point.

Usage: py probe_nonsquare_layout.py
"""
import numpy as np

from warplab import Lab, dense
import probe_presets_model as pm

BOXES = [
    (100, 100, 288, 288),
    (100, 100, 360, 216),
    (100, 100, 216, 360),
    (100, 100, 400, 300),
    (100, 100, 300, 400),
    (100, 100, 576, 288),
]


def flat_sample(box):
    lab = Lab(visible=True)
    try:
        tb = lab.textbox(pm.TEXT, box=box)
        flat = lab.bake(tb, flat=True)
    finally:
        lab.close()
    fs = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
    P = np.vstack([dense(s, 60) for s in fs])
    x0, x1 = P[:, 0].min(), P[:, 0].max()
    y0, y1 = P[:, 1].min(), P[:, 1].max()
    return P, (P[:, 0] - x0) / (x1 - x0), (P[:, 1] - y0) / (y1 - y0), (x1 - x0, y1 - y0)


def main():
    refP, refU, refV, refSize = flat_sample(BOXES[0])
    print(f"reference {BOXES[0][2]}x{BOXES[0][3]}: {len(refP)} points, "
          f"ink {refSize[0]:.4f} x {refSize[1]:.4f} pt")
    print(f"{'box':12s} {'points':>6s} {'ink W':>9s} {'ink H':>9s} "
          f"{'dU max':>9s} {'dV max':>9s} {'dUV rms':>9s}")
    for box in BOXES:
        P, U, V, size = flat_sample(box)
        if P.shape == refP.shape:
            dU, dV = np.abs(U - refU), np.abs(V - refV)
            rms = np.sqrt((dU ** 2 + dV ** 2).mean() / 2)
            print(f"{box[2]}x{box[3]:7d} {len(P):6d} {size[0]:9.4f} {size[1]:9.4f} "
                  f"{dU.max():9.6f} {dV.max():9.6f} {rms:9.6f}")
        else:
            print(f"{box[2]}x{box[3]:7d} {len(P):6d} {size[0]:9.4f} {size[1]:9.4f} "
                  f"point count differs: {P.shape} vs {refP.shape}")


if __name__ == "__main__":
    main()
