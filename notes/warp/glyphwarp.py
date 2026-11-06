"""Print the exact warped coordinates of a glyph's edges under the measured polar map.

Part of the glyph catalogue in this folder. Requires glyphscan.py in the same directory.
Usage:
    py glyphwarp.py                 # the worked examples in GLYPH-CATALOGUE.md
    py glyphwarp.py "Segoe UI Symbol" 0x25B2
"""
import os, sys, math, json
sys.stdout.reconfigure(encoding='utf-8')
D = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, D)
from glyphscan import GeoPen, open_faces, FONTS, analyze_contour

def get_font(label):
    for lab, path, idx in FONTS:
        if lab == label:
            return open_faces(path)[idx][1]
    raise KeyError(label)

def warped(label, cp, maxedges=40):
    font = get_font(label)
    cmap = font.getBestCmap() or {}
    if cp not in cmap:
        print(f"U+{cp:04X} missing in {label}"); return
    gs = font.getGlyphSet()
    pen = GeoPen(gs, 24)
    gs[cmap[cp]].draw(pen); pen._flush()
    pts = [p for c in pen.contours for p in c["pts"]]
    x0, x1 = min(p[0] for p in pts), max(p[0] for p in pts)
    y0, y1 = min(p[1] for p in pts), max(p[1] for p in pts)
    W, H = x1-x0, y1-y0
    print(f"\n=== U+{cp:04X} {chr(cp)} in {label}  ink {W:.0f}x{H:.0f} ===")
    for ci, c in enumerate(pen.contours):
        cc = analyze_contour(c)
        kind = cc["cls"]
        print(f" contour {ci}: {kind}, {c['nseg']} segs, closed={c['closed']}")
        if kind in ("poly", "polycirc"):
            n = 0
            cpts = c["pts"] + [c["pts"][0]] if c["closed"] else c["pts"]
            for i in range(1, len(cpts)):
                p, q = cpts[i-1], cpts[i]
                u1, v1 = (p[0]-x0)/W, (p[1]-y0)/H
                u2, v2 = (q[0]-x0)/W, (q[1]-y0)/H
                du, dv = u2-u1, v2-v1
                if abs(du) < 1e-9 and abs(dv) < 1e-9: continue
                n += 1
                if n > maxedges: break
                if abs(dv) < 1e-9:
                    r = 1 - v1/2
                    th1, th2 = math.pi + 2*math.pi*u1, math.pi + 2*math.pi*u2
                    print(f"   H  u {u1:+.3f}->{u2:+.3f} v={v1:+.3f}: arc r={r:.4f} "
                          f"theta {th1/math.pi:+.3f}pi -> {th2/math.pi:+.3f}pi span {abs(th2-th1)*180/math.pi:.2f} deg")
                elif abs(du) < 1e-9:
                    th = math.pi + 2*math.pi*u1
                    r1, r2 = 1 - v1/2, 1 - v2/2
                    print(f"   V  u={u1:+.3f} v {v1:+.3f}->{v2:+.3f}: ray theta={th/math.pi:+.3f}pi "
                          f"r {r1:.4f}->{r2:.4f}")
                else:
                    a, h = abs(du), abs(dv)
                    v0 = min(v1, v2)
                    q1 = a*(1+v0)/h
                    q2 = q1 + a
                    lam = h/(4*math.pi*a)
                    us = u1 if v1 <= v2 else u2
                    kappa = 2*math.pi*(q1-us) - math.pi
                    chir = "rising" if dv > 0 else "falling/mirror"
                    print(f"   S  ({u1:+.3f},{v1:+.3f})->({u2:+.3f},{v2:+.3f}) {chir}: "
                          f"spiral window psi=[{2*math.pi*q1:.4f},{2*math.pi*q2:.4f}] rad, "
                          f"lambda={lam:.4f}, kappa={kappa/math.pi:+.3f}pi, q=({q1:.4f},{q2:.4f})")
        elif kind in ("circ", "ell"):
            fit = cc.get("circ") if kind == "circ" else cc.get("ell")
            if fit:
                if kind == "circ":
                    print(f"   circle centre u={(fit['cx']-x0)/W:+.3f} v={(fit['cy']-y0)/H:+.3f} "
                          f"r_u={fit['r']/W:.4f} r_v={fit['r']/H:.4f} dev={100*fit['dev']:.3f}%")
                else:
                    print(f"   ellipse centre u={(fit['cx']-x0)/W:+.3f} v={(fit['cy']-y0)/H:+.3f} "
                          f"rx_u={fit['rx']/W:.4f} ry_v={fit['ry']/H:.4f} dev={100*fit['dev']:.3f}%")
        else:
            print(f"   (not a primitive)")

EX = [(0x25A0,"Segoe UI Symbol"),(0x25A1,"Segoe UI Symbol"),(0x2500,"Segoe UI Symbol"),
      (0x2502,"Segoe UI Symbol"),(0x2550,"Segoe UI Symbol"),(0x25B2,"Segoe UI Symbol"),
      (0x25E2,"Segoe UI Symbol"),(0x2571,"Consolas"),(0x2630,"Segoe UI Symbol"),
      (0x00D7,"Segoe UI Symbol"),(0x2295,"MS Gothic"),(0x25CB,"Segoe UI Symbol"),
      (0x25CF,"Segoe UI Symbol"),(0x283F,"Segoe UI Symbol"),(0x2685,"Segoe UI Symbol")]
if __name__ == "__main__":
    if len(sys.argv) >= 3:
        warped(sys.argv[1], int(sys.argv[2], 0))
    else:
        for cp, f in EX:
            warped(f, cp)
