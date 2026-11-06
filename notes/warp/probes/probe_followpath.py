"""Probe 6: Follow Path presets (textArchUp, textArchDown, textCircle, textButton) -- not
settable by COM, so set in XML (observation only; they are the 'Follow Path' row of the
Transform gallery). Question: are glyphs bent (a map of the plane) or moved rigidly?
Test: per glyph, fit the best rigid motion (Procrustes, no scale) and the best similarity
from flat corners to warped nodes; report residuals."""
import sys, matplotlib
matplotlib.use("Agg"); import matplotlib.pyplot as plt
from warplab import *
from scipy.spatial import cKDTree
text = sys.argv[1] if len(sys.argv) > 1 else "▦▦▦▦"
presets = sys.argv[2:] or ["textArchUp", "textArchDown", "textCircle", "textButton"]
BOX = (100, 100, 288, 288)
for pr in presets:
    lab = Lab(visible=True)
    try:
        tb = lab.textbox(text, size=40, box=BOX)
        flat = lab.bake(tb, flat=True)
        xml_edit_reopen(lab, set_warp_xml(pr))
        warped = lab.bake(lab.s.Shapes(1))
    finally:
        lab.close()
    fig, ax = plt.subplots(figsize=(7, 7))
    for s_ in warped: D = dense(s_, 20); ax.plot(D[:, 0], D[:, 1], "k-", lw=1)
    def kabsch(A, B, scale):
        ma, mb = A.mean(0), B.mean(0); Hm = (A - ma).T @ (B - mb)
        U_, S_, Vt = np.linalg.svd(Hm); d = np.sign(np.linalg.det(Vt.T @ U_.T))
        D_ = np.diag([1, d]); R = Vt.T @ D_ @ U_.T
        sc = (S_ * np.diag(D_)).sum() / ((A - ma) ** 2).sum() if scale else 1.0
        res = np.hypot(*((sc * (A - ma) @ R.T + mb) - B).T)
        return res.max(), sc, np.degrees(np.arctan2(R[1, 0], R[0, 0]))
    worst = 0; scs = []; angs = []
    fc = [corners(s_) for s_ in flat]; wc = [corners(s_) for s_ in warped]
    for i, A in enumerate(fc):
        cands = [B for B in wc if len(B) == len(A)]
        best = None
        for B in cands:
            for k in range(len(B)):
                for Bk in (np.roll(B, k, 0), np.roll(B[::-1], k, 0)):
                    r = kabsch(A, Bk, False)
                    if best is None or r[0] < best[0]: best = r + (kabsch(A, Bk, True)[1],)
        worst = max(worst, best[0]); scs.append(best[3]); angs.append(best[2])
    print(f"{pr:13s} contours={len(fc)}/{len(wc)} rigid fit worst={worst:.3f} pt, "
          f"free-scale range {min(scs):.4f}..{max(scs):.4f}, rotations {sorted(set(np.round(angs,2)))[:6]}...")
    ax.set_aspect("equal"); ax.invert_yaxis(); ax.set_title(pr); fig.savefig(f"follow_{pr}.png", dpi=80)
