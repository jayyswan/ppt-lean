"""Plot flat->predicted vs PowerPoint's warped outline for one preset (debug aid)."""
import sys, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from warplab import *
text, pr, mode = sys.argv[1], sys.argv[2], (sys.argv[3] if len(sys.argv) > 3 else "arclen")
out = sys.argv[4] if len(sys.argv) > 4 else f"plot_{pr}.png"
BOX = (100, 100, 288, 288)
lab = Lab()
try:
    tb = lab.textbox(text, box=BOX)
    flat = lab.bake(tb, flat=True); ink = inkbox(flat)
    warped = lab.bake(tb, warp=pr)
finally:
    lab.close()
F = model_fn(pr, BOX, ink, mode)
fig, ax = plt.subplots(figsize=(8, 8))
for s in warped:
    D = dense(s, 30); ax.plot(D[:, 0], D[:, 1], "k-", lw=1.5)
for s in flat:
    D = np.array([F(p) for p in dense(s, 30)]); ax.plot(D[:, 0], D[:, 1], "r--", lw=0.8)
    D = dense(s, 2); ax.plot(D[:, 0], D[:, 1], ":", color="0.7", lw=0.6)
for pc in paths(pr, *BOX[2:], None, *BOX[:2]):
    g = Guide(pc); G = np.array([g.at(s) for s in np.linspace(0, 1, 200)]); ax.plot(G[:, 0], G[:, 1], "b-", lw=0.5)
ax.add_patch(plt.Rectangle(BOX[:2], *BOX[2:], fill=False, ec="g", lw=0.5))
ax.set_aspect("equal"); ax.invert_yaxis(); ax.set_title(f"{pr} {mode}: black=PPT, red=model, blue=guides")
fig.savefig(out, dpi=90)
print(out, "ink", np.round(ink, 2))
