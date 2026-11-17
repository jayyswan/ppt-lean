"""Probe 22: the full Equalize band-height table H(n), n = drawn size in pixels (0.75 pt),
for one font. Sizes are set as the 0.1 pt spinner value that draws at n. Rows of mixed sizes
(the band does not depend on the row, probe 20). Output: equalize_table_<FONT>.json {n: H}.
Usage: py probe_equalize_table.py [FONT] [NMAX]"""
import sys, json, time
from warplab import *
font = sys.argv[1] if len(sys.argv) > 1 else "Segoe UI Symbol"
nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 5333
fn = "equalize_table_%s.json" % font.replace(" ", "")
try: table = {int(k): v for k, v in json.load(open(fn)).items()}
except FileNotFoundError: table = {}
todo = [n for n in range(2, nmax + 1) if n not in table]
lab = Lab(visible=True); t0 = time.time()


def run(ns):
    tb = lab.textbox("H" * len(ns), font=font, size=10, box=(0, 0, 500, 500))
    tr = tb.TextFrame.TextRange
    for i, n in enumerate(ns): tr.Characters(i + 1, 1).Font.Size = round(0.75 * n, 1)
    tb.TextFrame2.TextRange.Font.Equalize = -1
    subs = sorted(lab.bake(tb, flat=True), key=lambda s: dense(s, 10)[:, 0].min()); tb.Delete()
    if len(subs) != len(ns):
        if len(ns) == 1: return
        h = len(ns) // 2; run(ns[:h]); run(ns[h:]); return
    for n, s in zip(ns, subs):
        D = dense(s, 20); table[n] = round((D[:, 1].max() - D[:, 1].min()) / 0.75)


try:
    for i in range(0, len(todo), 40):
        run(todo[i:i + 40])
        if (i // 40) % 10 == 0:
            json.dump(table, open(fn, "w")); print(f"{len(table)} sizes, {time.time() - t0:.0f}s", flush=True)
finally:
    json.dump(table, open(fn, "w")); lab.close()
print("done", len(table))
