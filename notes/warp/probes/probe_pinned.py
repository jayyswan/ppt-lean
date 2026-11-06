"""Probe 5: circle glyphs under a warp with a chosen handle value (set in XML, observation
only), compared with the predicted ideal image of the *idealized* circle.
Usage: py probe_pinned.py PRESET ADJ TEXT [FONT]; ADJ is 100000 or adj1=..,adj2=.."""
import sys, json, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
from warplab import *
from scipy.spatial import cKDTree
pr, adjs, text = sys.argv[1], sys.argv[2], sys.argv[3]
ADJ = dict((kv.split("=") if "=" in kv else ("adj", kv)) for kv in adjs.split(","))
ADJ = {k: int(v) for k, v in ADJ.items()}; adjv = adjs.replace(",", "_").replace("=", "")
font = sys.argv[4] if len(sys.argv) > 4 else "Segoe UI Symbol"
BOX = (100, 100, 288, 288)
lab = Lab(visible=True)
try:
    tb = lab.textbox(text, font=font, box=BOX)
    tb.TextFrame2.WarpFormat = WARP_ID[pr]
    flat = lab.bake(tb, flat=True)
    xml_edit_reopen(lab, set_warp_xml(pr, ADJ))
    tb = lab.s.Shapes(1)
    warped = lab.bake(tb)
    print("stored:", re.findall(r'prstTxWarp prst="\w+">(.*?)</a:prstTxWarp>', lab.slide_xml(), re.S))
finally:
    lab.close()
ink = inkbox(flat); x0, y0, x1, y1 = ink
ps = paths(pr, 288, 288, ADJ, 100, 100); gt, gb = Guide(ps[0]), Guide(ps[1])
F = lambda u, v: warp_point(gt, gb, u, v, "arclen")
WD = np.vstack([dense(s, 60) for s in warped])
fig, ax = plt.subplots(figsize=(8, 8))
for s in warped: D = dense(s, 30); ax.plot(D[:, 0], D[:, 1], "k-", lw=1.4)
report = []
for s in flat:  # fit an ideal circle (in u, v) to each flat contour and warp it exactly
    P = dense(s, 30); U = (P[:, 0] - x0) / (x1 - x0); V = (P[:, 1] - y0) / (y1 - y0)
    cu, cv = (U.max() + U.min()) / 2, (V.max() + V.min()) / 2; ru, rv = np.ptp(U) / 2, np.ptp(V) / 2
    th = np.linspace(0, 2 * np.pi, 1500)
    I = np.array([F(cu + ru * np.cos(t), cv + rv * np.sin(t)) for t in th])
    d1 = cKDTree(WD).query(I)[0]
    ax.plot(I[:, 0], I[:, 1], "r--", lw=0.8)
    report.append(dict(centre_uv=(round(cu, 4), round(cv, 4)), radii_uv=(round(ru, 4), round(rv, 4)),
                       ideal_vs_ppt_max=round(float(d1.max()), 3), rms=round(float(np.sqrt((d1**2).mean())), 3)))
for r in report: print(r)
ax.set_aspect("equal"); ax.invert_yaxis(); ax.set_title(f"{pr} adj={adjv} {text}: black PPT, red ideal circle image")
fig.savefig(f"pinned_{pr}_{adjv}.png", dpi=90)
