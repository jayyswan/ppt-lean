"""Probe 39b: is a box-size change only an affine map of PowerPoint's outline?

Bakes the same text and preset at two box sizes, then fits the best affine map from
one PowerPoint outline to the other.  The map is sampled at the same normalized ink
points at both sizes.  The Lean/Python warp model is used only to place those sample
points; each sample is then snapped to the nearest point of PowerPoint's baked outline,
and the affine fit and residual use the PowerPoint points.

For a control, the same fit is also done from model point to model point.  A large
PowerPoint residual with a small model residual and small model-to-PowerPoint match
error is direct evidence that PowerPoint itself is not merely affinely rescaling the
outline when the box aspect ratio changes.

PowerPoint's 48/49 span slip contaminates this comparison: if one size spans only
48/49 of a guide, the residual measures that bug as well as the aspect-ratio change.
The probe therefore fits the per-guide fill fractions `(kT, kB)` at each size (probe
33's method) and marks a case `*` when either size is near 48/49, including the waves'
`0.99589 × 48/49 ≈ 0.9756` variant.  Use the model-only probe for the uncontaminated
mathematical answer; use this probe's clean rows for PowerPoint evidence.

Usage:
  py probe_affine_ppt.py [--all-stops] [--pair WxH:WxH ...] [PRESET ...]

Default pair: 288x288 -> 360x216.  `--pair` may be repeated.  Results go to
affine_box_ppt.json.
"""
import argparse
import json
import sys

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import cKDTree

from warplab import *
import probe_presets_model as pm


def parse_size(text):
    w, h = text.lower().split("x")
    return float(w), float(h)


def parse_pair(text):
    a, b = text.split(":")
    return parse_size(a), parse_size(b)


def default_cases(names):
    for k in names:
        spec, h1, *h2 = pm.PRESETS[k]
        v1 = h1[1]
        v2 = h2[0][1] if h2 else 0
        yield k, spec, "default", v1, "default", v2


def affine_residual(P, Q):
    X = np.column_stack([P, np.ones(len(P))])
    coef, *_ = np.linalg.lstsq(X, Q, rcond=None)
    R = X @ coef - Q
    return np.linalg.norm(R, axis=1)


def bake_sample(preset, spec, v1, v2, box, uv=None):
    """Bake one PowerPoint state.  Return model points, matched PPT points, and errors.

    `uv` is the common normalized ink frame.  The first size establishes it from the
    idealized flat glyphs; the second size reuses it so the two maps see the same ink
    point.  PowerPoint is only read here; no measured handle state is created.
    """
    lab = Lab(visible=True)
    try:
        tb = lab.textbox(pm.TEXT, box=box)
        tb.TextFrame2.WarpFormat = WARP_ID[spec]
        flat = lab.bake(tb, flat=True)
        xml_edit_reopen(lab, set_warp_xml(spec, pm.stored_adj(spec, v1, v2)))
        tb = lab.s.Shapes(1)
        warped = lab.bake(tb)
        L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height
    finally:
        lab.close()

    if len(flat) != len(pm.TEXT):
        raise RuntimeError(f"expected {len(pm.TEXT)} flat contours, got {len(flat)}")
    fs = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
    I = np.vstack([pm.ideal_pieces(cn, ch)[0] for ch, cn in zip(pm.TEXT, fs)])
    x0, x1 = I[:, 0].min(), I[:, 0].max()
    y0, y1 = I[:, 1].min(), I[:, 1].max()
    ownU, ownV = (I[:, 0] - x0) / (x1 - x0), (I[:, 1] - y0) / (y1 - y0)
    U, V = uv if uv is not None else (ownU, ownV)

    gt, gb = pm.guides(preset, v1 / 100000, v2 / 100000, W, H)
    M = (1 - V)[:, None] * gt(U) + V[:, None] * gb(U) + np.array([L, T])
    WD = np.vstack([dense(s, 80) for s in warped])
    P = WD[cKDTree(WD).query(M)[1]]
    return dict(U=U, V=V, ownU=ownU, ownV=ownV, M=M, P=P,
                match=np.linalg.norm(P - M, axis=1),
                gt=gt, gb=gb, WD=WD, L=L, T=T, W=W, H=H, n=len(U))


def fit_fill(sample, mask=None):
    """Fit how much of each guide PowerPoint actually spans (probe 33's kT, kB)."""
    U, V = sample["ownU"], sample["ownV"]
    if mask is not None:
        U, V = U[mask], V[mask]
    gt, gb, WD = sample["gt"], sample["gb"], sample["WD"]
    offset = np.array([sample["L"], sample["T"]])
    tree = cKDTree(WD)

    def err(p):
        kt, kb = p
        Mp = ((1 - V)[:, None] * gt(np.clip(kt * U, 0, 1))
              + V[:, None] * gb(np.clip(kb * U, 0, 1)) + offset)
        return float(np.sqrt((tree.query(Mp)[0] ** 2).mean()))

    starts = [(1, 1), (48 / 49, 1), (1, 48 / 49), (48 / 49, 48 / 49)]
    best = min((minimize(err, x0=g, method="Nelder-Mead",
                         options=dict(xatol=1e-5, fatol=1e-6)) for g in starts),
               key=lambda r: r.fun)
    return float(best.x[0]), float(best.x[1])


WAVE_SLIP = 48 / 49 * 0.99589  # wave span = 48/49 times the usual Bézier underestimate


def has_48_49(preset, kT, kB, tol=2e-3):
    """The 48/49 slip, including the waves' 0.99589 times 48/49 variant."""
    targets = [48 / 49]
    if preset.startswith(("wave", "doubleWave")):
        targets.append(WAVE_SLIP)
    return any(abs(k - target) < tol for k in (kT, kB) for target in targets)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("presets", nargs="*", help="preset names; default: all")
    ap.add_argument("--all-stops", action="store_true",
                    help="every reachable stop instead of the default handles")
    ap.add_argument("--pair", action="append", default=[],
                    help="WxH:WxH, repeatable (default 288x288:360x216)")
    ap.add_argument("--out", default="affine_box_ppt.json")
    args = ap.parse_args()

    names = args.presets or list(pm.PRESETS)
    bad = [k for k in names if k not in pm.PRESETS]
    if bad:
        raise SystemExit(f"unknown preset(s): {', '.join(bad)}")
    pairs = [parse_pair(p) for p in args.pair] or [((288, 288), (360, 216))]
    cases = pm.cases(names) if args.all_stops else default_cases(names)

    out = []
    slipped = 0
    print(f"{'preset':24s} {'handles':13s} {'sizes':16s} {'n':>5s} "
          f"{'model max':>9s} {'ppt max':>9s} {'match A':>8s} {'match B':>8s}")
    for k, spec, s1, v1, s2, v2 in cases:
        for (w0, h0), (w1, h1) in pairs:
            try:
                A = bake_sample(k, spec, v1, v2, (100, 100, w0, h0))
                B = bake_sample(k, spec, v1, v2, (100, 100, w1, h1),
                                uv=(A["U"], A["V"]))
                kTa, kBa = fit_fill(A)
                kTb, kBb = fit_fill(B)
                slip_a = has_48_49(k, kTa, kBa)
                slip_b = has_48_49(k, kTb, kBb)
                slip = slip_a or slip_b
                slipped += int(slip)
                rm = affine_residual(A["M"], B["M"])
                rp = affine_residual(A["P"], B["P"])
                rec = dict(preset=k, spec=spec, handle1=s1, handle2=s2,
                           adj1=v1, adj2=v2,
                           base=[w0, h0], target=[w1, h1], n=A["n"],
                           model_max=float(rm.max()),
                           model_rms=float(np.sqrt((rm ** 2).mean())),
                           ppt_max=float(rp.max()),
                           ppt_rms=float(np.sqrt((rp ** 2).mean())),
                           ppt_max_frac=float(rp.max() / max(w1, h1)),
                           match_a_max=float(A["match"].max()),
                           match_b_max=float(B["match"].max()),
                           k_a=[kTa, kBa], k_b=[kTb, kBb],
                           slip_48_49=bool(slip))
            except Exception as exc:  # keep a long probe running; record the failure
                rec = dict(preset=k, spec=spec, handle1=s1, handle2=s2,
                           adj1=v1, adj2=v2, base=[w0, h0], target=[w1, h1],
                           error=repr(exc))
            out.append(rec)
            with open(args.out, "w", encoding="utf-8") as f:
                json.dump(out, f, indent=1)
            if "error" in rec:
                print(f"{k:24s} {s1 + '/' + s2:13s} ERROR {rec['error']}")
            else:
                sizes = f"{int(w0)}x{int(h0)}->{int(w1)}x{int(h1)}"
                flag = "*" if rec["slip_48_49"] else " "
                print(f"{k:24s} {s1 + '/' + s2:13s} {sizes:16s} {rec['n']:5d} "
                      f"{rec['model_max']:9.4f} {rec['ppt_max']:9.4f} "
                      f"{rec['match_a_max']:8.4f} {rec['match_b_max']:8.4f} {flag}")
                if rec["slip_48_49"]:
                    print(f"    * 48/49 span: A k=({rec['k_a'][0]:.5f}, "
                          f"{rec['k_a'][1]:.5f}) B k=({rec['k_b'][0]:.5f}, "
                          f"{rec['k_b'][1]:.5f})")
    print(f"\n{slipped} case(s) flagged with the 48/49 span artifact")
    print(f"wrote {args.out}")


if __name__ == "__main__":
    main()
