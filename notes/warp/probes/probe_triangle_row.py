"""Probe 38: a row of N Lower Right Triangles (U+25E2) through the modelled warps, so every
slanted edge is short. The row is laid out with the Lean rules (pen step snap(1764 s / 2048),
verified exact by probe 36), its ink box normalized to the unit square, and each triangle's three
edges sent through the ruled map (arcTrace-style arc-length guides of probe_presets_model). The image
is compared with PowerPoint's baked outline, max distance each way, and the slanted edges
alone are reported separately.
Usage: py probe_triangle_row.py [N] [size] -> triangle_row.json"""
import sys, json
import numpy as np
from scipy.spatial import cKDTree
from warplab import *
import probe_presets_model as M

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8
SIZE = float(sys.argv[2]) if len(sys.argv) > 2 else 36.0
snap = lambda x: 0.75 * np.floor(x / 0.75 + 0.5)
s = SIZE / 2048
step = snap(1764 * SIZE / 2048)
tris = []   # each triangle: three vertices, y up in font units -> slide-like coords (y down, baseline 0)
for i in range(N):
    p = i * step
    tris.append([(p + 1599 * s, -1434 * s), (p + 1599 * s, 0.0), (p + 165 * s, 0.0)])
allv = np.array([v for t in tris for v in t])
x0, x1, y0, y1 = allv[:, 0].min(), allv[:, 0].max(), allv[:, 1].min(), allv[:, 1].max()
def edges(t, n=200):
    out = {}
    for name, (a, b) in dict(vert=(t[0], t[1]), base=(t[1], t[2]), slant=(t[2], t[0])).items():
        a, b = np.array(a), np.array(b); w = np.linspace(0, 1, n)[:, None]
        out[name] = (1 - w) * a + w * b
    return out
CASES = [("warpUp", (288, 288)), ("warpDown", (288, 288)), ("ringOutside", (288, 288)), ("archWarped", (288, 288)),
         ("waveDown", (360, 216)), ("inflate", (288, 288)), ("deflate", (288, 288)), ("curveUp", (288, 288)),
         ("inflateTop", (288, 288)), ("triangleUp", (288, 288)), ("square", (288, 288))]
OUT = []
lab = Lab(visible=True)
try:
    for k, (bw, bh) in CASES:
        spec, h1, *h2 = M.PRESETS[k]
        tb = lab.textbox("◢" * N, size=SIZE, box=(100, 100, bw, bh))
        tb.TextFrame2.WarpFormat = WARP_ID[spec]
        warped = lab.bake(tb); L, T, W, H = tb.Left, tb.Top, tb.Width, tb.Height; tb.Delete()
        gt, gb = M.guides(k, h1[1] / 1e5, (h2[0][1] if h2 else 0) / 1e5, W, H)
        def F(P):
            u = (P[:, 0] - x0) / (x1 - x0); v = (P[:, 1] - y0) / (y1 - y0)
            return (1 - v)[:, None] * gt(np.clip(u, 0, 1)) + v[:, None] * gb(np.clip(u, 0, 1)) + np.array([L, T])
        D = np.vstack([dense(sub, 80) for sub in warped]); tree = cKDTree(D)
        res = {}
        for name in ("vert", "base", "slant"):
            Mp = np.vstack([F(edges(t)[name]) for t in tris]); res[name] = tree.query(Mp)[0]
        Mall = np.vstack([F(edges(t)[n]) for t in tris for n in ("vert", "base", "slant")])
        back = cKDTree(Mall).query(D)[0]
        r = dict(preset=k, box=(W, H), N=N, size=SIZE, ncontours=len(warped),
                 slant_max=round(float(res["slant"].max()), 2), slant_rms=round(float(np.sqrt((res["slant"] ** 2).mean())), 2),
                 vert_max=round(float(res["vert"].max()), 2), base_max=round(float(res["base"].max()), 2),
                 ppt_to_model_max=round(float(back.max()), 2))
        print(r, flush=True); OUT.append(r)
finally:
    lab.close()
json.dump(OUT, open("triangle_row.json", "w"), indent=1)
