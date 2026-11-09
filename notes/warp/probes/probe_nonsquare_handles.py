"""Probe 40c: do the handle laws survive non-square boxes?

For each selected preset, bakes every reachable stop setting in landscape and portrait
boxes, fits the per-guide fill factors, and reports the model error before and after
that fit.  A large fit-k error means the handle/guide rule itself is wrong; a small one
means only the span factor differs.  Rows marked `*` are 48/49-contaminated.

Usage: py probe_nonsquare_handles.py [PRESET ...]
"""
import sys

import numpy as np
from scipy.spatial import cKDTree

import probe_presets_model as pm
import probe_affine_ppt as pa

BOXES = {
    "archWarped": [(320, 240), (240, 320)],
    "archWarpedDown": [(240, 320), (384, 288)],
    "warpedCircle": [(320, 240), (240, 320)],
    "warpedButton": [(320, 240), (240, 320)],
    "ringInside": [(320, 240), (384, 288)],
    "ringOutside": [(320, 240), (384, 288)],
    "warpUp": [(320, 240), (288, 384)],
    "warpDown": [(320, 240), (240, 320)],
    "waveDown": [(320, 240), (240, 320)],
    "waveUp": [(320, 240), (240, 320)],
    "deflateBottom": [(320, 240), (240, 320)],
    "stop": [(320, 240), (240, 320)],
}
NAMES = list(BOXES)


def fit_residual(S, kT, kB):
    U, V = S["ownU"], S["ownV"]
    M = ((1 - V)[:, None] * S["gt"](np.clip(kT * U, 0, 1))
         + V[:, None] * S["gb"](np.clip(kB * U, 0, 1)) + np.array([S["L"], S["T"]]))
    d = cKDTree(S["WD"]).query(M)[0]
    return float(d.max()), float(np.sqrt((d ** 2).mean()))


def main():
    names = sys.argv[1:] or NAMES
    print(f"{'preset':18s} {'handles':13s} {'box':9s} {'kT':>8s} {'kB':>8s} "
          f"{'k1 max':>8s} {'fit max':>8s} {'fit rms':>8s} {'slip':>5s}")
    for k in names:
        spec, h1, *h2 = pm.PRESETS[k]
        for kk, spec2, s1, v1, s2, v2 in pm.cases([k]):
            for w, h in BOXES.get(k, [(320, 240), (240, 320)]):
                try:
                    S = pa.bake_sample(kk, spec2, v1, v2, (100, 100, w, h))
                    kT, kB = pa.fit_fill(S)
                    fmx, frms = fit_residual(S, kT, kB)
                    slip = pa.has_48_49(k, kT, kB)
                    print(f"{k:18s} {s1 + '/' + s2:13s} {w}x{h:<5d} "
                          f"{kT:8.5f} {kB:8.5f} {S['match'].max():8.4f} "
                          f"{fmx:8.4f} {frms:8.4f} {str(slip):>5s}")
                except Exception as exc:
                    print(f"{k:18s} {s1 + '/' + s2:13s} {w}x{h:<5d} ERROR {exc!r}")


if __name__ == "__main__":
    main()
