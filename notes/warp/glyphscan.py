"""Classify installed font glyphs by whether their outlines decompose into geometric primitives.

Part of the glyph catalogue in this folder. Requires fontTools and numpy. The scan writes
one JSON record per (font, code point) with per-contour classes and fits; the catalogue
pipeline (`export.py`) then picks the best face per code point.

Usage:  py glyphscan.py
The FONTS list below is the 29-face set measured for the catalogue. Add or remove faces
as needed; the font paths are Windows-specific.
"""
import os, sys, json, math, time
import numpy as np
from fontTools.ttLib import TTFont, TTCollection
from fontTools.pens.basePen import BasePen

TOL = 1.0
D = os.path.dirname(os.path.abspath(__file__))

FONTS = [
    ("Segoe UI Symbol", r"C:\Windows\Fonts\seguisym.ttf", 0),
    ("Cambria", r"C:\Windows\Fonts\cambria.ttc", 0),
    ("Cambria Math", r"C:\Windows\Fonts\cambria.ttc", 1),
    ("Cascadia Code", r"C:\Windows\Fonts\CascadiaCode.ttf", 0),
    ("Consolas", r"C:\Windows\Fonts\consola.ttf", 0),
    ("Arial", r"C:\Windows\Fonts\arial.ttf", 0),
    ("Times New Roman", r"C:\Windows\Fonts\times.ttf", 0),
    ("Calibri", r"C:\Windows\Fonts\calibri.ttf", 0),
    ("Tahoma", r"C:\Windows\Fonts\tahoma.ttf", 0),
    ("Lucida Sans Unicode", r"C:\Windows\Fonts\l_10646.ttf", 0),
    ("Segoe UI", r"C:\Windows\Fonts\segoeui.ttf", 0),
    ("Segoe UI Emoji", r"C:\Windows\Fonts\seguiemj.ttf", 0),
    ("MS Gothic", r"C:\Windows\Fonts\msgothic.ttc", 0),
    ("Yu Gothic", r"C:\Windows\Fonts\YuGothR.ttc", 0),
    ("Microsoft YaHei", r"C:\Windows\Fonts\msyh.ttc", 0),
    ("Malgun Gothic", r"C:\Windows\Fonts\malgun.ttf", 0),
    ("SimSun", r"C:\Windows\Fonts\simsun.ttc", 0),
    ("Meiryo", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\Meiryo\31055294773.ttf", 0),
    ("MS Mincho", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\MS Mincho\37327920121.ttf", 0),
    ("Batang", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\Batang\39569681348.ttf", 0),
    ("Noto Sans", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\Noto Sans\24003405683.ttf", 0),
    ("Lato", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\Lato\25090817022.ttf", 0),
    ("Verdana", r"C:\Windows\Fonts\verdana.ttf", 0),
    ("Georgia", r"C:\Windows\Fonts\georgia.ttf", 0),
    ("Courier New", r"C:\Windows\Fonts\cour.ttf", 0),
    ("Century Gothic", r"C:\Windows\Fonts\GOTHIC.TTF", 0),
    ("Franklin Gothic Book", r"C:\Windows\Fonts\FRABK.TTF", 0),
    ("Book Antiqua", r"C:\Windows\Fonts\BKANT.TTF", 0),
    ("Yu Mincho", r"C:\Users\<user>\AppData\Local\Microsoft\FontCache\4\CloudFonts\Yu Mincho\31868023978.ttf", 0),
]

def open_faces(path):
    if path.lower().endswith((".ttc", ".otc")):
        return [(i, f) for i, f in enumerate(TTCollection(path, lazy=True).fonts)]
    return [(0, TTFont(path, lazy=True, fontNumber=0))]

def family_name(f):
    try:
        for rec in f["name"].names:
            if rec.nameID == 4:
                return str(rec.toUnicode())
    except Exception:
        pass
    return "?"

class GeoPen(BasePen):
    def __init__(self, glyphSet, samples=24):
        super().__init__(glyphSet)
        self.samples = samples
        self.contours = []
        self.cur = None
    def _new(self, p):
        self.cur = {"pts": [tuple(p)], "has_curve": False, "closed": False, "nseg": 0}
    def _flush(self):
        if self.cur and len(self.cur["pts"]) > 1:
            self.contours.append(self.cur)
        self.cur = None
    def _moveTo(self, p):
        self._flush(); self._new(p)
    def _lineTo(self, p):
        if self.cur is None: self._new(p)
        self.cur["pts"].append(tuple(p)); self.cur["nseg"] += 1
    def _qCurveToOne(self, p1, p2):
        if self.cur is None: self._new(p1)
        p0 = self.cur["pts"][-1]
        for i in range(1, self.samples + 1):
            t = i / self.samples
            self.cur["pts"].append(((1-t)**2*p0[0] + 2*(1-t)*t*p1[0] + t*t*p2[0],
                                    (1-t)**2*p0[1] + 2*(1-t)*t*p1[1] + t*t*p2[1]))
        self.cur["has_curve"] = True; self.cur["nseg"] += 1
    def _curveToOne(self, p1, p2, p3):
        if self.cur is None: self._new(p1)
        p0 = self.cur["pts"][-1]
        for i in range(1, self.samples + 1):
            t = i / self.samples
            self.cur["pts"].append((((1-t)**3*p0[0] + 3*(1-t)**2*t*p1[0]
                                     + 3*(1-t)*t*t*p2[0] + t**3*p3[0]),
                                    ((1-t)**3*p0[1] + 3*(1-t)**2*t*p1[1]
                                     + 3*(1-t)*t*t*p2[1] + t**3*p3[1])))
        self.cur["has_curve"] = True; self.cur["nseg"] += 1
    def _closePath(self):
        if self.cur is not None:
            self.cur["closed"] = True; self._flush()
    def _endPath(self):
        self._flush()

def circle_fit(pts):
    P = np.asarray(pts, float)
    if len(P) < 3: return None
    x, y = P[:, 0], P[:, 1]
    A = np.column_stack([2*x, 2*y, np.ones_like(x)])
    b = x*x + y*y
    try:
        sol, *_ = np.linalg.lstsq(A, b, rcond=None)
    except Exception:
        return None
    cx, cy, c = sol
    r2 = c + cx*cx + cy*cy
    if not np.isfinite(r2) or r2 <= 0: return None
    r = math.sqrt(r2)
    d = np.hypot(x-cx, y-cy)
    return {"cx": float(cx), "cy": float(cy), "r": float(r),
            "dev": float(np.max(np.abs(d-r))/r),
            "rms": float(np.sqrt(np.mean((d-r)**2))/r)}

def ellipse_fit(pts):
    P = np.asarray(pts, float)
    if len(P) < 6: return None
    x, y = P[:, 0], P[:, 1]
    A = np.column_stack([y*y, x, y, np.ones_like(x)])
    b = -(x*x)
    try:
        sol, *_ = np.linalg.lstsq(A, b, rcond=None)
    except Exception:
        return None
    a, bb, cc, dd = sol
    if not np.isfinite(a) or abs(a) < 1e-12: return None
    cx, cy = -bb/2, -cc/(2*a)
    rx2 = cx*cx + a*cy*cy - dd
    ry2 = rx2/a
    if rx2 <= 0 or ry2 <= 0: return None
    rx, ry = math.sqrt(rx2), math.sqrt(ry2)
    val = ((x-cx)/rx)**2 + ((y-cy)/ry)**2
    return {"cx": float(cx), "cy": float(cy), "rx": float(rx), "ry": float(ry),
            "dev": float(np.max(np.abs(np.sqrt(np.maximum(val, 0)) - 1)))}

def trimmed_circle(pts):
    """Least squares with iterative trimming; returns fit, inlier mask, turning."""
    P = np.asarray(pts, float)
    n = len(P)
    if n < 8: return None
    mask = np.ones(n, bool)
    fit = None
    for _ in range(5):
        sub = P[mask]
        if len(sub) < 6: return None
        fit = circle_fit(sub)
        if fit is None: return None
        d = np.hypot(P[:, 0]-fit["cx"], P[:, 1]-fit["cy"])
        res = np.abs(d-fit["r"])
        thr = max(0.01*fit["r"], float(np.percentile(res[mask], 80)))
        new = res <= thr
        if new.sum() < 8: return None
        if np.array_equal(new, mask): break
        mask = new
    dev = float(np.max(np.abs(np.hypot(P[mask, 0]-fit["cx"], P[mask, 1]-fit["cy"])-fit["r"])) / fit["r"])
    sgn, ab = turning(P, fit, mask)
    return {"cx": fit["cx"], "cy": fit["cy"], "r": fit["r"], "dev": dev,
            "frac": float(mask.sum())/n, "turn": sgn, "abs": ab}

def turning(pts, fitted, mask=None):
    if not fitted: return 0.0, 0.0
    cx, cy = fitted["cx"], fitted["cy"]
    ang = [math.atan2(p[1]-cy, p[0]-cx) for p in pts]
    sgn = ab = 0.0
    for i in range(1, len(ang)):
        if mask is not None and not (mask[i] and mask[i-1]):
            continue
        d = ang[i]-ang[i-1]
        while d > math.pi: d -= 2*math.pi
        while d < -math.pi: d += 2*math.pi
        sgn += d; ab += abs(d)
    return sgn, ab


def _area(pts):
    a = 0.0
    for i in range(len(pts)):
        x1, y1 = pts[i-1]; x2, y2 = pts[i]
        a += x1*y2 - x2*y1
    return abs(a)/2.0

def _hull(pts):
    P = sorted(set((round(x, 6), round(y, 6)) for x, y in pts))
    if len(P) < 3: return P
    def cross(o, a, b):
        return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
    lo = []
    for p in P:
        while len(lo) >= 2 and cross(lo[-2], lo[-1], p) <= 0: lo.pop()
        lo.append(p)
    up = []
    for p in reversed(P):
        while len(up) >= 2 and cross(up[-2], up[-1], p) <= 0: up.pop()
        up.append(p)
    return lo[:-1] + up[:-1]

def convex_ratio(pts):
    a = _area(pts)
    h = _area(_hull(pts))
    return (a/h) if h > 1e-9 else 0.0

def analyze_contour(c):
    pts0 = c["pts"]
    pts = pts0 + [pts0[0]] if c["closed"] else pts0
    xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
    W, H = max(xs)-min(xs), max(ys)-min(ys)
    diag = math.hypot(W, H)
    out = {"closed": c["closed"], "has_curve": c["has_curve"], "nseg": c["nseg"],
           "W": W, "H": H, "diag": diag, "bbox": [min(xs), min(ys), max(xs), max(ys)]}
    cf = circle_fit(pts)
    if cf:
        out["circ"] = {k: cf[k] for k in ("cx", "cy", "r", "dev")}
        sgn, ab = turning(pts, cf)
        out["turn"] = sgn
    ef = ellipse_fit(pts)
    if ef:
        out["ell"] = {k: ef[k] for k in ("cx", "cy", "rx", "ry", "dev")}
    if not c["has_curve"]:
        h = v = d = o = 0
        for i in range(1, len(pts)):
            dx = pts[i][0]-pts[i-1][0]; dy = pts[i][1]-pts[i-1][1]
            if abs(dx) <= TOL and abs(dy) <= TOL: continue
            if abs(dy) <= TOL: h += 1
            elif abs(dx) <= TOL: v += 1
            elif abs(abs(dx)-abs(dy)) <= TOL: d += 1
            else: o += 1
        out["nseg"] = len(pts) - 1
        out.update({"poly": True, "h": h, "vert": v, "diag_edges": d, "other": o,
                    "axis": (d == 0 and o == 0 and (h+v) > 0)})
        if (cf and cf["dev"] < 0.01 and out["nseg"] >= 8
                and abs(out.get("turn", 0)) > 1.6*math.pi
                and 0.65 <= cf["r"]/(0.5*diag) <= 1.5):
            out["polycirc"] = True
    else:
        out["poly"] = False
    turn = abs(out.get("turn", 0.0))
    rsize = (cf["r"]/(0.5*diag)) if (cf and diag > 1e-9) else 0.0
    if not c["has_curve"]:
        out["cls"] = "polycirc" if out.get("polycirc") else "poly"
        return out
    if (cf and cf["dev"] < 0.01 and turn >= 1.75*math.pi
            and 0.65 <= rsize <= 1.5):
        out["cls"] = "circ"; return out
    if (cf and cf["dev"] < 0.01 and turn >= 0.45*math.pi
            and rsize >= 0.45):
        out["cls"] = "arc"; return out
    if (ef and ef["dev"] < 0.01 and turn >= 1.75*math.pi and c["closed"]
            and 0.5 <= ef["rx"]/(0.5*diag) <= 1.6
            and 0.35 <= ef["ry"]/(0.5*diag) <= 1.6):
        out["cls"] = "ell"; return out
    tc = trimmed_circle(pts)
    if tc:
        out["trim"] = {k: tc[k] for k in ("cx", "cy", "r", "dev", "frac")}
        out["trim_turn"] = tc["turn"]
        conv = convex_ratio(pts)
    out["conv"] = conv
    if (tc["dev"] < 0.01 and tc["frac"] >= 0.70
                and 0.55 <= tc["r"]/(0.5*diag) <= 1.6
                and conv >= 0.85 and turn < 1.75*math.pi
                and abs(tc["turn"]) >= 0.40*math.pi
                and abs(tc["turn"]) <= 1.75*math.pi):
            out["cls"] = "cap"; return out
    if c["closed"] and turn < 0.55*math.pi and diag > 0 and _area(pts) < 0.15*W*H + 1e-9:
        out["cls"] = "sliver"; return out
    out["cls"] = "free"; return out

def analyze(font, cp):
    cmap = font.getBestCmap() or {}
    if cp not in cmap: return None
    gs = font.getGlyphSet()
    pen = GeoPen(gs, samples=24)
    try:
        gs[cmap[cp]].draw(pen); pen._flush()
    except Exception:
        return None
    if not pen.contours: return None
    cs = [analyze_contour(c) for c in pen.contours]
    kinds = [c["cls"] for c in cs]
    # glyph diagonal
    allpts = [p for c in pen.contours for p in c["pts"]]
    xs = [p[0] for p in allpts]; ys = [p[1] for p in allpts]
    gdiag = math.hypot(max(xs)-min(xs), max(ys)-min(ys))
    nfree = kinds.count("free")
    big_free = sum(1 for c in cs if c["cls"] == "free" and c["diag"] >= 0.40*gdiag)
    npoly = sum(k in ("poly", "polycirc") for k in kinds)
    ncirc = kinds.count("circ")
    nell = kinds.count("ell")
    narc = kinds.count("arc")
    ncap = kinds.count("cap")
    nsliver = kinds.count("sliver")
    all_axis = all(c.get("axis") for c in cs if c["cls"] in ("poly", "polycirc"))
    circ_cs = [c for c in cs if c["cls"] == "circ"]
    ndots = 0
    if circ_cs:
        ref = max(circ_cs, key=lambda c: c["circ"]["r"])
        rx, ry, rr = ref["circ"]["cx"], ref["circ"]["cy"], ref["circ"]["r"]
        ndots = sum(1 for c in circ_cs
                    if math.hypot(c["circ"]["cx"]-rx, c["circ"]["cy"]-ry) > 0.15*rr)
    # tier
    if nfree == 0 and (npoly + ncirc + nell + narc + ncap) > 0:
        if ncirc + nell + narc + ncap == 0:
            gcls = "axis" if all_axis else "polygon"
            tier = "P"
        elif len(cs) == 1:
            gcls = {"circ": "circle", "ell": "ellipse", "arc": "arc", "cap": "semicircle"}.get(kinds[0], "polygon")
            tier = "C"
        elif npoly == 0 and ncap + narc == 0:
            if nell == 0:
                gcls = "dots" if ndots > 0 else "circle"
            else:
                gcls = "dots" if ndots > 0 else "ellipse"
            tier = "C"
        else:
            gcls = "compound"; tier = "K"
    else:
        gcls = "mixed"; tier = "X"
    big_circle = any(c["cls"] in ("circ", "cap") and c["diag"] >= 0.45*gdiag for c in cs)
    return {"gcls": gcls, "tier": tier, "ncontours": len(cs), "nfree": nfree,
            "big_free": big_free, "npoly": npoly, "ncirc": ncirc, "nell": nell,
            "narc": narc, "ncap": ncap, "nsliver": nsliver, "ndots": ndots, "gdiag": gdiag,
            "big_circle": big_circle, "cs": cs}

BLOCKS = [
    (0x0021, 0x007E, "Basic Latin"),
    (0x00A0, 0x00FF, "Latin-1 Supplement"),
    (0x2000, 0x206F, "General Punctuation"),
    (0x20A0, 0x20BF, "Currency Symbols"),
    (0x2100, 0x214F, "Letterlike Symbols"),
    (0x2190, 0x21FF, "Arrows"),
    (0x2200, 0x22FF, "Mathematical Operators"),
    (0x2300, 0x23FF, "Miscellaneous Technical"),
    (0x2460, 0x24FF, "Enclosed Alphanumerics"),
    (0x2500, 0x257F, "Box Drawing"),
    (0x2580, 0x259F, "Block Elements"),
    (0x25A0, 0x25FF, "Geometric Shapes"),
    (0x2600, 0x26FF, "Miscellaneous Symbols"),
    (0x2700, 0x27BF, "Dingbats"),
    (0x27C0, 0x27EF, "Miscellaneous Mathematical Symbols-A"),
    (0x27F0, 0x27FF, "Supplemental Arrows-A"),
    (0x2800, 0x28FF, "Braille Patterns"),
    (0x2900, 0x297F, "Supplemental Arrows-B"),
    (0x2980, 0x29FF, "Miscellaneous Mathematical Symbols-B"),
    (0x2A00, 0x2AFF, "Supplemental Mathematical Operators"),
    (0x2B00, 0x2BFF, "Miscellaneous Symbols and Arrows"),
    (0x2E00, 0x2E7F, "Supplemental Punctuation"),
    (0x3000, 0x303F, "CJK Symbols and Punctuation"),
    (0xFE10, 0xFE19, "Vertical Forms"),
    (0xFE30, 0xFE4F, "CJK Compatibility Forms"),
    (0xFF01, 0xFF5E, "Halfwidth and Fullwidth Forms"),
    (0xFFE0, 0xFFEE, "Halfwidth and Fullwidth Forms"),
    (0x1F700, 0x1F77F, "Alchemical Symbols"),
    (0x1F780, 0x1F7FF, "Geometric Shapes Extended"),
    (0x1F800, 0x1F8FF, "Supplemental Arrows-C"),
    (0x1FA00, 0x1FA6F, "Chess Symbols"),
    (0x1FB00, 0x1FBFF, "Symbols for Legacy Computing"),
]

def load_cps():
    """The scanned code points: every assigned character in BLOCKS."""
    import unicodedata
    out = []
    for lo, hi, block in BLOCKS:
        for cp in range(lo, hi + 1):
            ch = chr(cp)
            if unicodedata.category(ch) == "Cn":
                continue
            out.append({"cp": cp, "name": unicodedata.name(ch, ""), "block": block})
    return out

def main():
    cps = load_cps()
    outpath = os.path.join(D, "glyphs-scan.jsonl")
    with open(outpath, "w", encoding="utf-8") as out:
        for label, path, faceidx in FONTS:
            t0 = time.time()
            if not os.path.exists(path):
                print("MISSING", label); continue
            try:
                font = open_faces(path)[faceidx][1]
                upem = font["head"].unitsPerEm
                fam = family_name(font)
            except Exception as e:
                print("ERR open", label, e); continue
            n = 0
            for item in cps:
                try:
                    d = analyze(font, item["cp"])
                except Exception:
                    continue
                if d is None: continue
                rec = {"font": label, "family": fam, "face": faceidx,
                       "cp": item["cp"], "name": item["name"],
                       "block": item["block"], "upem": upem}
                rec.update(d)
                out.write(json.dumps(rec, ensure_ascii=False) + "\n")
                n += 1
            print(f"{label}: {n} glyphs, {time.time()-t0:.1f}s", flush=True)
    print("done", outpath)

if __name__ == "__main__":
    main()
