"""Probe 35: the Full Block through the modelled warps. A lone block's ink box is the block, so
its corners are (u, v) in {0,1}^2 and the ruled map predicts them exactly. Compared with the
nearest node of PowerPoint's baked outline (edges are under-subdivided by PowerPoint, so only
corners are tested). Also: two touching blocks merge into one contour of the predicted width.
Usage: py probe_block_warp.py  -> block_warp.json"""
import json
import numpy as np
from scipy.spatial import cKDTree
from warplab import *
import probe_presets_model as M

OUT = []
lab = Lab(visible=True)
try:
    # overlap: "██" at 72 pt, no spacing: one merged contour; width from the Lean model
    tb = lab.textbox("██", size=72, box=(100, 100, 600, 200))
    subs = lab.bake(tb, flat=True); tb.Delete()
    P = np.vstack([dense(s, 20) for s in subs])
    snap = lambda x: 0.75 * np.floor(x / 0.75 + 0.5)
    step = snap(1921 * 72 / 2048)
    pred_w = step + 1931 * 72 / 2048 + 10 * 72 / 2048
    print("two blocks:", len(subs), "contour(s); width", round(float(np.ptp(P[:, 0])), 4),
          "pred", round(float(pred_w), 4))
    OUT.append(dict(test="two touching blocks", contours=len(subs), width=float(np.ptp(P[:, 0])),
                    pred=float(pred_w)))
    for k in ["triangleUp", "square", "stop", "fadeRight", "slantUp", "warpUp", "warpDown", "ringInside",
              "archWarped", "archWarpedDown", "warpedCircle", "waveDown", "doubleWaveUpDown", "inflate",
              "deflate", "curveUp", "inflateTop", "deflateTopInflateBottom"]:
        spec, h1, *h2 = M.PRESETS[k]
        for box in [(100, 100, 288, 288), (100, 100, 360, 216)]:
            tb = lab.textbox("█", size=72, box=box)
            tb.TextFrame2.WarpFormat = WARP_ID[spec]
            warped = lab.bake(tb); L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height; tb.Delete()
            gt, gb = M.guides(k, h1[1] / 1e5, (h2[0][1] if h2 else 0) / 1e5, W, H)
            C = []
            for u in (0., 1.):
                for v in (0., 1.):
                    C.append((1 - v) * gt(np.array([u]))[0] + v * gb(np.array([u]))[0] + np.array([L, T]))
            C = np.array(C)
            N = np.vstack([nodes(s) for s in warped])
            d = cKDTree(N).query(C)[0]
            r = dict(preset=k, box=(W, H), corner_err=[round(float(x), 2) for x in d], max=round(float(d.max()), 2))
            print(r, flush=True); OUT.append(r)
finally:
    lab.close()
json.dump(OUT, open("block_warp.json", "w"), indent=1)
