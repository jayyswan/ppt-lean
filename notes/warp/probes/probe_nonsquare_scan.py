"""Probe 40d: find non-square boxes with kT/kB near 1, for the presets whose 5:3 rows
are 48/49-contaminated.

Usage: py probe_nonsquare_scan.py [PRESET ...]
Default boxes: 320x240, 240x320, 384x288, 288x384.
"""
import sys

import numpy as np

import probe_presets_model as pm
import probe_affine_ppt as pa

DEFAULT_BOXES = [(320, 240), (240, 320), (384, 288), (288, 384)]
DEFAULT_PRESETS = ["archWarpedDown", "warpUp", "warpDown", "ringInside", "ringOutside",
                   "warpedCircle", "waveDown", "curveUp"]


def main():
    names = sys.argv[1:] or DEFAULT_PRESETS
    print(f"{'preset':22s} {'box':10s} {'kT':>8s} {'kB':>8s} {'k1 max':>8s} {'slip':>5s}")
    for k in names:
        spec, h1, *h2 = pm.PRESETS[k]
        v1, v2 = h1[1], (h2[0][1] if h2 else 0)
        for w, h in DEFAULT_BOXES:
            try:
                S = pa.bake_sample(k, spec, v1, v2, (100, 100, w, h))
                kT, kB = pa.fit_fill(S)
                slip = pa.has_48_49(k, kT, kB)
                print(f"{k:22s} {w}x{h:<6d} {kT:8.5f} {kB:8.5f} "
                      f"{S['match'].max():8.3f} {str(slip):>5s}")
            except Exception as exc:
                print(f"{k:22s} {w}x{h:<6d} ERROR {exc!r}")


if __name__ == "__main__":
    main()
