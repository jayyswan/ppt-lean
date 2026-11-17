"""Probe 1: the map law. For each preset, bake a test string flat and warped and score the
ruled-map model F(u,v) = (1-v) P_top(u) + v P_bot(u) under each guide parametrization.
Usage: py probe_maplaw.py [text] [preset ...]"""
import sys, json
from warplab import *
text = sys.argv[1] if len(sys.argv) > 1 else "▦"
presets = sys.argv[2:] or list(WARP_ID)
BOX = (100, 100, 288, 288)
lab = Lab()
res = {}
try:
    tb = lab.textbox(text, box=BOX)
    flat = lab.bake(tb, flat=True)
    ink = inkbox(flat)
    for pr in presets:
        warped = lab.bake(tb, warp=pr)
        npath = len(paths(pr, 288, 288))
        row = {}
        for mode in ("param", "visual", "arclen", "x"):
            try:
                row[mode] = score(model_fn(pr, BOX, ink, mode), flat, warped)
            except Exception as e:
                row[mode] = {"err": repr(e)}
        best = min((m for m in row if "edge_max" in row[m]), key=lambda m: row[m]["edge_max"])
        res[pr] = row
        print(f"{pr:27s} paths={npath} best={best:6s} " + "  ".join(
            f"{m}:{row[m].get('corner_max', float('nan')):6.2f}/{row[m].get('edge_max', float('nan')):6.2f}"
            for m in row), flush=True)
finally:
    lab.close()
json.dump(res, open(f"maplaw_{ord(text[0]):04X}.json", "w"), indent=1)
