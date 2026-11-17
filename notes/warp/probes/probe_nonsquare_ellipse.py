"""Probe 40b: which parameterization does PowerPoint use on non-square ellipse guides?

For the elliptic/polar presets, bakes one clean non-square box, then fits each of
`param`, `visual`, and `arclen` with per-guide fill factors kT, kB.  The mode with the
small residual after fitting k is the one PowerPoint is using.

Usage: py probe_nonsquare_ellipse.py
"""
import numpy as np
from scipy.optimize import minimize
from scipy.spatial import cKDTree

from warplab import Guide, dense, paths
import probe_presets_model as pm
import probe_affine_ppt as pa

CASES = [
    ("archWarped", (320, 240)),
    ("archWarpedDown", (240, 320)),
    ("warpUp", (320, 240)),
    ("warpDown", (320, 240)),
    ("ringInside", (320, 240)),
    ("ringOutside", (320, 240)),
    ("warpedCircle", (320, 240)),
    ("warpedButton", (320, 240)),
]

MODES = ("param", "visual", "arclen")


def gat(guide, s, mode):
    """Vectorized `Guide.at`."""
    return np.array([guide.at(float(x), mode) for x in s])


def fitted(gt, gb, U, V, WD, L, T, mode, stride=4):
    tree = cKDTree(WD)
    off = np.array([L, T])
    Us, Vs = U[::stride], V[::stride]

    def err(p):
        kt, kb = p
        M = ((1 - Vs)[:, None] * gat(gt, np.clip(kt * Us, 0, 1), mode)
             + Vs[:, None] * gat(gb, np.clip(kb * Us, 0, 1), mode) + off)
        return float(np.sqrt((tree.query(M)[0] ** 2).mean()))

    starts = [(1, 1), (0.98, 1), (1, 0.98), (0.976, 0.976)]
    best = min((minimize(err, x0=g, method="Nelder-Mead",
                         options=dict(xatol=1e-5, fatol=1e-6)) for g in starts),
               key=lambda r: r.fun)
    kt, kb = best.x
    M = ((1 - V)[:, None] * gat(gt, np.clip(kt * U, 0, 1), mode)
         + V[:, None] * gat(gb, np.clip(kb * U, 0, 1), mode) + off)
    d = tree.query(M)[0]
    return float(kt), float(kb), float(d.max()), float(np.sqrt((d ** 2).mean()))


def main():
    print(f"{'preset':20s} {'box':9s} {'mode':7s} {'kT':>8s} {'kB':>8s} "
          f"{'max':>8s} {'rms':>8s}")
    for k, (w, h) in CASES:
        spec, h1, *h2 = pm.PRESETS[k]
        v1, v2 = h1[1], (h2[0][1] if h2 else 0)
        S = pa.bake_sample(k, spec, v1, v2, (100, 100, w, h))
        ps = paths(spec, S["W"], S["H"], pm.stored_adj(spec, v1, v2))
        gt, gb = Guide(ps[0]), Guide(ps[1])
        print(f"{k:20s} {w}x{h:<5d} {'lean':7s} {'':>8s} {'':>8s} "
              f"{S['match'].max():8.4f} {np.sqrt((S['match'] ** 2).mean()):8.4f}")
        for mode in MODES:
            kt, kb, mx, rms = fitted(gt, gb, S["ownU"], S["ownV"], S["WD"],
                                     S["L"], S["T"], mode)
            print(f"{'':20s} {'':9s} {mode:7s} {kt:8.5f} {kb:8.5f} "
                  f"{mx:8.4f} {rms:8.4f}")
        print()


if __name__ == "__main__":
    main()
