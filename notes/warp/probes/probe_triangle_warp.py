"""Probe 37: the Lower Right Triangle (U+25E2) through the modelled warps. A lone triangle's ink
box is its bounding box, so its corners are (u, v) = (1, 0), (1, 1), (0, 1) and its slanted edge
is v = 1 - u. Both go through the ruled map exactly. Reported: corner error (to the nearest node
of PowerPoint's baked outline) and the slanted edge's image, sampled densely, against PowerPoint's
outline (max distance each way). PowerPoint refits long edges with a few Beziers, so edge
distances are looser than corner distances.
Usage: py probe_triangle_warp.py  -> triangle_warp.json"""
import json
import numpy as np
from scipy.spatial import cKDTree
from warplab import *
import probe_presets_model as M

OUT = []
PRESETS = ["triangleUp", "square", "stop", "fadeRight", "slantUp", "warpUp", "warpDown", "ringInside",
           "ringOutside", "archWarped", "archWarpedDown", "warpedCircle", "waveDown", "doubleWaveUpDown",
           "inflate", "deflate", "curveUp", "inflateTop", "deflateTopInflateBottom"]
lab = Lab(visible=True)
try:
    for k in PRESETS:
        spec, h1, *h2 = M.PRESETS[k]
        for box in [(100, 100, 288, 288), (100, 100, 360, 216)]:
            tb = lab.textbox("◢", size=72, box=box)
            tb.TextFrame2.WarpFormat = WARP_ID[spec]
            warped = lab.bake(tb); L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height; tb.Delete()
            gt, gb = M.guides(k, h1[1] / 1e5, (h2[0][1] if h2 else 0) / 1e5, W, H)
            F = lambda u, v: (1 - v) * gt(np.array([u]))[0] + v * gb(np.array([u]))[0] + np.array([L, T])
            C = np.array([F(1, 0), F(1, 1), F(0, 1)])
            N = np.vstack([nodes(s) for s in warped]); D = np.vstack([dense(s, 120) for s in warped])
            uu = np.linspace(0, 1, 400)
            E = np.array([F(u, 1 - u) for u in uu])
            ce = cKDTree(N).query(C)[0]; e1 = cKDTree(D).query(E)[0]
            r = dict(preset=k, box=(W, H), corners=[round(float(x), 2) for x in ce],
                     edge_model_to_ppt=round(float(e1.max()), 2), edge_rms=round(float(np.sqrt((e1 ** 2).mean())), 2))
            print(r, flush=True); OUT.append(r)
finally:
    lab.close()
json.dump(OUT, open("triangle_warp.json", "w"), indent=1)
