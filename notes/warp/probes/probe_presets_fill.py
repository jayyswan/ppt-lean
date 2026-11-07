"""Probe 33: for the cases of probe 32 that miss, fit a fill fraction per guide: the text
spans only `kT` of the top guide's arc length and `kB` of the bottom's (from the start).
Tests the hypothesis that PowerPoint sometimes drops one of 49 pieces of a guide (k = 48/49),
the span artifact of `notes/spiral/F1.md` (e).
Usage: py probe_presets_fill.py PRESET H1 H2 W H [...]   (H1/H2 = min|default|max)"""
import sys, json
import numpy as np
from scipy.spatial import cKDTree
from scipy.optimize import minimize
from warplab import *
import probe_presets_model as M

args = sys.argv[1:]; out = []
for i in range(0, len(args), 5):
    k, s1, s2, W, H = args[i:i + 5]; W, H = float(W), float(H)
    spec, h1, *h2 = M.PRESETS[k]; h2 = h2[0] if h2 else (None, 0, None)
    idx = {"min": 0, "default": 1, "max": 2}
    v1, v2 = h1[idx[s1]], h2[idx[s2]]
    lab = Lab(visible=True)
    try:
        tb = lab.textbox(M.TEXT, box=(100, 100, W, H)); tb.TextFrame2.WarpFormat = WARP_ID[spec]
        flat = lab.bake(tb, flat=True)
        xml_edit_reopen(lab, set_warp_xml(spec, M.stored_adj(spec, v1, v2))); tb = lab.s.Shapes(1)
        warped = lab.bake(tb)
    finally:
        lab.close()
    fs = sorted(flat, key=lambda s: dense(s, 10)[:, 0].mean())
    I = np.vstack([M.ideal_pieces(cn, ch)[0] for ch, cn in zip(M.TEXT, fs)])
    x0, x1, y0, y1 = I[:, 0].min(), I[:, 0].max(), I[:, 1].min(), I[:, 1].max()
    U, V = (I[:, 0] - x0) / (x1 - x0), (I[:, 1] - y0) / (y1 - y0)
    gt, gb = M.guides(k, v1 / 1e5, v2 / 1e5, W, H)
    WD = np.vstack([dense(s, 80) for s in warped]); tree = cKDTree(WD)
    def err(p, full=False):
        kt, kb = p
        Mp = (1 - V)[:, None] * gt(np.clip(kt * U, 0, 1)) + V[:, None] * gb(np.clip(kb * U, 0, 1)) + 100
        d2 = cKDTree(Mp).query(WD)[0]
        return (d2.max(), np.sqrt((d2 ** 2).mean())) if full else np.sqrt((d2 ** 2).mean())
    best = min((minimize(err, x0=g, method="Nelder-Mead", options=dict(xatol=1e-5, fatol=1e-6)) for g in
                [(1, 1), (48 / 49, 1), (1, 48 / 49), (48 / 49, 48 / 49)]), key=lambda r: r.fun)
    r = dict(preset=k, h1=s1, h2=s2, box=(W, H), unfit=[round(x, 3) for x in err((1, 1), True)],
             kT=round(best.x[0], 5), kB=round(best.x[1], 5), fit=[round(x, 3) for x in err(best.x, True)],
             at_48_49=dict((lab_, [round(x, 3) for x in err(p, True)]) for lab_, p in
                           [("T", (48 / 49, 1)), ("B", (1, 48 / 49)), ("TB", (48 / 49, 48 / 49))]))
    print(r, flush=True); out.append(r)
json.dump(out, open("presets_fill.json", "w"), indent=1)
