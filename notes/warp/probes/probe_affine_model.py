"""Probe 39a: does changing the box size add more than an affine map?

Pure model check, no PowerPoint.  Samples `WarpPreset.map` on a grid of normalized
ink coordinates `(u, v)` at two box sizes, then fits the best affine map from the
first image to the second.  A zero residual means the size change is only an affine
map; a nonzero residual means the map itself changed.  This is the idealization
`k = 1`; PowerPoint's occasional 48/49 span slip is absent here and is handled by
probe 39b.

Usage:
  py probe_affine_model.py [--all-stops] [--pair WxH:WxH ...] [PRESET ...]

Default pair: 288x288 -> 360x216.  `--pair` may be repeated.  Results go to
affine_box_model.json.
"""
import argparse
import json
import sys

import numpy as np

import probe_presets_model as pm


def parse_size(text):
    w, h = text.lower().split("x")
    return float(w), float(h)


def parse_pair(text):
    a, b = text.split(":")
    return parse_size(a), parse_size(b)


def sample_map(preset, a, b, w, h, n=81):
    u = np.linspace(0, 1, n)
    v = np.linspace(0, 1, n)
    U, V = np.meshgrid(u, v, indexing="ij")
    U, V = U.ravel(), V.ravel()
    gt, gb = pm.guides(preset, a, b, w, h)
    P = (1 - V)[:, None] * gt(U) + V[:, None] * gb(U)
    return P


def affine_residual(P, Q):
    X = np.column_stack([P, np.ones(len(P))])
    coef, *_ = np.linalg.lstsq(X, Q, rcond=None)
    R = X @ coef - Q
    return np.linalg.norm(R, axis=1)


def default_cases(names):
    for k in names:
        spec, h1, *h2 = pm.PRESETS[k]
        v1 = h1[1]
        v2 = h2[0][1] if h2 else 0
        yield k, spec, "default", v1, "default", v2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("presets", nargs="*", help="preset names; default: all")
    ap.add_argument("--all-stops", action="store_true",
                    help="every reachable stop instead of the default handles")
    ap.add_argument("--pair", action="append", default=[],
                    help="WxH:WxH, repeatable (default 288x288:360x216)")
    ap.add_argument("--grid", type=int, default=81, help="grid points per side")
    ap.add_argument("--out", default="affine_box_model.json")
    args = ap.parse_args()

    names = args.presets or list(pm.PRESETS)
    bad = [k for k in names if k not in pm.PRESETS]
    if bad:
        raise SystemExit(f"unknown preset(s): {', '.join(bad)}")
    pairs = [parse_pair(p) for p in args.pair] or [((288, 288), (360, 216))]
    cases = pm.cases(names) if args.all_stops else default_cases(names)

    out = []
    print(f"{'preset':24s} {'handles':13s} {'sizes':16s} {'n':>5s} "
          f"{'max pt':>9s} {'max/scale':>10s} {'rms/scale':>10s}")
    for k, spec, s1, v1, s2, v2 in cases:
        a, b = v1 / 100000, v2 / 100000
        for (w0, h0), (w1, h1) in pairs:
            P = sample_map(k, a, b, w0, h0, args.grid)
            Q = sample_map(k, a, b, w1, h1, args.grid)
            r = affine_residual(P, Q)
            scale = max(w1, h1)
            rec = dict(preset=k, spec=spec, handle1=s1, handle2=s2, adj1=v1, adj2=v2,
                       base=[w0, h0], target=[w1, h1], n=len(P),
                       max_pt=float(r.max()), rms_pt=float(np.sqrt((r ** 2).mean())),
                       max_frac=float(r.max() / scale),
                       rms_frac=float(np.sqrt((r ** 2).mean()) / scale))
            out.append(rec)
            sizes = f"{int(w0)}x{int(h0)}->{int(w1)}x{int(h1)}"
            print(f"{k:24s} {s1 + '/' + s2:13s} {sizes:16s} "
                  f"{len(P):5d} {rec['max_pt']:9.4f} {rec['max_frac']:10.6f} "
                  f"{rec['rms_frac']:10.6f}")
            with open(args.out, "w", encoding="utf-8") as f:
                json.dump(out, f, indent=1)
    print(f"\nwrote {args.out}")


if __name__ == "__main__":
    main()
