"""warplab: ideal text-warp maps from the DrawingML spec, and PowerPoint bakes to test them.

Two halves:

* **Spec side (pure Python).** `guides(prst, w, h, adj)` evaluates the preset's guide
  formulas from ECMA-376 `presetTextWarpDefinitions.xml`; `paths(...)` turns its path list
  into explicit pieces (lines, quadratic/cubic Beziers, elliptic arcs); `Guide` evaluates a
  path at a fraction `s in [0,1]` under several candidate parametrizations; `warp_point`
  is the ruled map  F(u, v) = (1 - v) * P_top(u) + v * P_bot(u).

* **PowerPoint side (COM, observation only).** `Lab` opens a private presentation, makes a
  text box with given text/font/size/box, applies a warp preset, and *bakes* the warped and
  the flat outline (duplicate -> Merge Shapes Combine with a far-away dummy -> SaveCopyAs ->
  parse custGeom). Setting `WarpFormat` by COM is the same state as clicking the preset in
  Shape Format > Text Effects > Transform; nothing here is a construction step.

Coordinates are slide points, y down. `u` runs left->right over the ink box of the whole
text, `v` runs top->bottom over it (v = 0 is the ink top, which goes to the first path).
"""
import math, os, re, sys, zipfile, tempfile, urllib.request
import numpy as np

SPEC_URL = ("https://raw.githubusercontent.com/LibreOffice/core/master/oox/source/export/"
            "presetTextWarpDefinitions.xml")
SPEC_CACHE = os.path.join(tempfile.gettempdir(), "presetTextWarpDefinitions.xml")


def spec_xml():
    if not os.path.exists(SPEC_CACHE):
        urllib.request.urlretrieve(SPEC_URL, SPEC_CACHE)
    return open(SPEC_CACHE, encoding="utf-8").read()


# ---------------------------------------------------------------- spec evaluator
ANG = 60000.0  # DrawingML angle unit: 1/60000 degree


def _builtins(w, h, l=0.0, t=0.0):
    ss, ls = min(w, h), max(w, h)
    d = dict(w=w, h=h, l=l, t=t, r=l + w, b=t + h, hc=l + w / 2, vc=t + h / 2, ss=ss, ls=ls,
             cd2=10800000.0, cd4=5400000.0, cd8=2700000.0)
    d["3cd4"], d["3cd8"], d["5cd8"], d["7cd8"] = 16200000.0, 8100000.0, 13500000.0, 18900000.0
    for k in (2, 3, 4, 5, 6, 8, 10, 32):
        d[f"wd{k}"] = w / k
        d[f"hd{k}"] = h / k
    for k in (2, 4, 6, 8, 16, 32):
        d[f"ssd{k}"] = ss / k
    return d


def _ev(env, tok):
    try:
        return float(tok)
    except ValueError:
        return env[tok]


def _fmla(env, f):
    op, *a = f.split()
    x = [_ev(env, q) for q in a]
    rad = lambda q: q / ANG * math.pi / 180
    if op == "val": return x[0]
    if op == "*/": return x[0] * x[1] / x[2]
    if op == "+-": return x[0] + x[1] - x[2]
    if op == "+/": return (x[0] + x[1]) / x[2]
    if op == "?:": return x[1] if x[0] > 0 else x[2]
    if op == "abs": return abs(x[0])
    if op == "at2": return math.degrees(math.atan2(x[1], x[0])) * ANG
    if op == "cat2": return x[0] * math.cos(math.atan2(x[2], x[1]))
    if op == "sat2": return x[0] * math.sin(math.atan2(x[2], x[1]))
    if op == "cos": return x[0] * math.cos(rad(x[1]))
    if op == "sin": return x[0] * math.sin(rad(x[1]))
    if op == "tan": return x[0] * math.tan(rad(x[1]))
    if op == "max": return max(x[0], x[1])
    if op == "min": return min(x[0], x[1])
    if op == "mod": return math.sqrt(x[0] ** 2 + x[1] ** 2 + x[2] ** 2)
    if op == "pin": return x[0] if x[1] < x[0] else (x[2] if x[1] > x[2] else x[1])
    if op == "sqrt": return math.sqrt(x[0])
    raise ValueError(f)


def preset_body(prst):
    m = re.search(r"<%s>(.*?)</%s>" % (prst, prst), spec_xml(), re.S)
    if not m: raise KeyError(prst)
    return re.sub(r"<(/?)a:", r"<\1", m.group(1))


def guides(prst, w, h, adj=None, l=0.0, t=0.0):
    """Evaluate avLst then gdLst. `adj` overrides avLst values by name (raw 1/100000 units)."""
    body = preset_body(prst)
    env = _builtins(w, h, l, t)
    for name, f in re.findall(r'<gd name="(\w+)" fmla="([^"]+)"', body):
        if adj and name in adj and name.startswith("adj"):
            env[name] = float(adj[name]); continue
        env[name] = _fmla(env, f)
    return env


def default_adj(prst):
    av = preset_body(prst).split("</avLst>")[0]
    return {n: f for n, f in re.findall(r'<gd name="(\w+)" fmla="val ([^"]+)"', av)}


def paths(prst, w, h, adj=None, l=0.0, t=0.0):
    """Paths in slide coordinates: evaluated in the box's local frame (spec formulas assume
    l = t = 0, some guides omit `t`) and then translated by (l, t)."""
    off = np.array([l, t])
    def sh(pc):
        return (pc[0],) + tuple(q + off if isinstance(q, np.ndarray) else q for q in pc[1:])
    return [[sh(pc) for pc in p] for p in _paths_local(prst, w, h, adj)]


def _paths_local(prst, w, h, adj=None):
    """List of paths; each path is a list of pieces ('L', p0, p1) / ('Q', p0, c, p1) /
    ('C', p0, c1, c2, p1) / ('A', centre, wR, hR, stAng_rad, swAng_rad) (parametric angles)."""
    env = guides(prst, w, h, adj)
    body = preset_body(prst)
    out = []
    for pb in re.findall(r"<path\b[^>]*>(.*?)</path>", body, re.S):
        cur, pcs = None, []
        for c in re.finditer(r"<(moveTo|lnTo|quadBezTo|cubicBezTo)>(.*?)</\1>|<arcTo ([^/]*)/>", pb, re.S):
            if c.group(1):
                pts = [np.array([_ev(env, x), _ev(env, y)])
                       for x, y in re.findall(r'x="([\w.-]+)" y="([\w.-]+)"', c.group(2))]
                k = c.group(1)
                if k == "moveTo": cur = pts[0]
                elif k == "lnTo": pcs.append(("L", cur, pts[0])); cur = pts[0]
                elif k == "quadBezTo": pcs.append(("Q", cur, pts[0], pts[1])); cur = pts[1]
                else: pcs.append(("C", cur, pts[0], pts[1], pts[2])); cur = pts[2]
            else:
                at = dict(re.findall(r'(\w+)="([\w.-]+)"', c.group(3)))
                wR, hR = _ev(env, at["wR"]), _ev(env, at["hR"])
                st = math.radians(_ev(env, at["stAng"]) / ANG)
                sw = math.radians(_ev(env, at["swAng"]) / ANG)
                # DrawingML angles are visual; convert to the ellipse's parametric angle.
                par = lambda a: math.atan2(wR * math.sin(a), hR * math.cos(a))
                p0 = par(st)
                # unwrap the end parameter so it follows the sweep direction
                p1 = par(st + sw)
                turns = round((sw - (p1 - p0)) / (2 * math.pi))
                p1 += 2 * math.pi * turns
                ctr = cur - np.array([wR * math.cos(p0), hR * math.sin(p0)])
                pcs.append(("A", ctr, wR, hR, p0, p1, st, sw))
                cur = ctr + np.array([wR * math.cos(p1), hR * math.sin(p1)])
        out.append(pcs)
    return out


def _piece_pt(pc, s):
    k = pc[0]
    if k == "L": return pc[1] + s * (pc[2] - pc[1])
    if k == "Q": return (1 - s) ** 2 * pc[1] + 2 * s * (1 - s) * pc[2] + s * s * pc[3]
    if k == "C":
        return ((1 - s) ** 3 * pc[1] + 3 * s * (1 - s) ** 2 * pc[2] + 3 * s * s * (1 - s) * pc[3]
                + s ** 3 * pc[4])
    if k == "A":
        _, ctr, wR, hR, p0, p1, *_ = pc
        a = p0 + s * (p1 - p0)
        return ctr + np.array([wR * math.cos(a), hR * math.sin(a)])
    if k == "AV":  # elliptic arc, visual angle linear
        _, ctr, wR, hR, p0, p1, st, sw = pc
        a = st + s * sw
        r = 1 / math.hypot(math.cos(a) / wR, math.sin(a) / hR)
        return ctr + r * np.array([math.cos(a), math.sin(a)])
    raise ValueError(k)


class Guide:
    """A path with three candidate parametrizations by s in [0, 1]:
    'param'  - pieces get equal shares of s, each traversed by its own parameter
               (Bezier t, ellipse parametric angle);
    'visual' - as 'param' but arcs by visual (polar) angle;
    'arclen' - s is the arc-length fraction of the whole path;
    'x'      - the point whose x equals x_start + s * (x_end - x_start) (graph-like paths)."""

    def __init__(self, pieces, n=4000):
        self.pieces = pieces
        self.ss = np.linspace(0, 1, n + 1)
        self.pts = np.array([self.at(s, "param") for s in self.ss])
        seg = np.hypot(*np.diff(self.pts, axis=0).T)
        self.cum = np.concatenate([[0], np.cumsum(seg)]) / seg.sum()

    def at(self, s, mode="param"):
        if mode == "arclen":
            j = np.interp(s, self.cum, self.ss)
            return self.at(j, "param")
        if mode == "x":
            xs = self.pts[:, 0]
            x = xs[0] + s * (xs[-1] - xs[0])
            order = np.argsort(xs) if xs[-1] >= xs[0] else np.argsort(-xs)
            j = np.interp(x if xs[-1] >= xs[0] else -x, (xs if xs[-1] >= xs[0] else -xs)[order],
                          self.ss[order])
            return self.at(j, "param")
        n = len(self.pieces)
        i = min(int(s * n), n - 1)
        pc = self.pieces[i]
        if mode == "visual" and pc[0] == "A": pc = ("AV",) + pc[1:]
        return _piece_pt(pc, s * n - i)


def warp_point(gtop, gbot, u, v, mode="param"):
    return (1 - v) * gtop.at(u, mode) + v * gbot.at(u, mode)


# ---------------------------------------------------------------- PowerPoint side
WARP_ID = {
    "textStop": 1, "textTriangle": 2, "textTriangleInverted": 3, "textChevron": 4,
    "textChevronInverted": 5, "textRingInside": 6, "textRingOutside": 7, "textArchUpPour": 8,
    "textArchDownPour": 9, "textCirclePour": 10, "textButtonPour": 11, "textCurveUp": 12,
    "textCurveDown": 13, "textCanUp": 14, "textCanDown": 15, "textWave1": 16, "textWave2": 17,
    "textDoubleWave1": 18, "textWave4": 19, "textInflate": 20, "textDeflate": 21,
    "textInflateBottom": 22, "textDeflateBottom": 23, "textInflateTop": 24, "textDeflateTop": 25,
    "textDeflateInflate": 26, "textDeflateInflateDeflate": 27, "textFadeRight": 28,
    "textFadeLeft": 29, "textFadeUp": 30, "textFadeDown": 31, "textSlantUp": 32,
    "textSlantDown": 33, "textCascadeUp": 34, "textCascadeDown": 35, "textPlain": 36,
}


def _parse_geom(xml_sp):
    off = re.search(r'<a:off x="(-?\d+)" y="(-?\d+)"', xml_sp)
    ext = re.search(r'<a:ext cx="(\d+)" cy="(\d+)"', xml_sp)
    ox, oy = int(off.group(1)), int(off.group(2))
    cx, cy = int(ext.group(1)), int(ext.group(2))
    subs = []
    for pm in re.finditer(r'<a:path w="(\d+)" h="(\d+)"[^>]*>(.*?)</a:path>', xml_sp, re.S):
        pw, ph = int(pm.group(1)), int(pm.group(2))
        P = lambda x, y: np.array([(ox + int(x) * cx / pw) / 12700.0, (oy + int(y) * cy / ph) / 12700.0])
        cur = None
        for c in re.finditer(r'<a:(moveTo|lnTo|cubicBezTo|quadBezTo|close)\b([^>]*?)(/>|>(.*?)</a:\1>)',
                             pm.group(3), re.S):
            k = c.group(1)
            pts = [P(*q) for q in re.findall(r'<a:pt x="(-?\d+)" y="(-?\d+)"', c.group(4) or "")]
            if k == "moveTo": cur = [("M", pts[0])]; subs.append(cur)
            elif k == "lnTo": cur.append(("L", pts[0]))
            elif k == "cubicBezTo": cur.append(("C",) + tuple(pts))
            elif k == "quadBezTo": cur.append(("Q",) + tuple(pts))
            else: cur.append(("Z",))
    return subs


def nodes(sub):
    return np.array([c[-1] for c in sub if c[0] in "MLCQ"])


def dense(sub, n=40):
    out, cur, start = [], None, None
    for c in sub:
        if c[0] == "M": cur = start = c[1]; out.append(cur)
        elif c[0] == "L":
            out += [cur + (c[1] - cur) * t for t in np.linspace(0, 1, n)[1:]]; cur = c[1]
        elif c[0] == "Q":
            p1, p2 = c[1], c[2]
            out += [(1 - t) ** 2 * cur + 2 * t * (1 - t) * p1 + t * t * p2 for t in np.linspace(0, 1, n)[1:]]
            cur = p2
        elif c[0] == "C":
            p1, p2, p3 = c[1], c[2], c[3]
            out += [(1 - t) ** 3 * cur + 3 * t * (1 - t) ** 2 * p1 + 3 * t * t * (1 - t) * p2 + t ** 3 * p3
                    for t in np.linspace(0, 1, n)[1:]]
            cur = p3
        elif c[0] == "Z" and cur is not None and start is not None:
            out += [cur + (start - cur) * t for t in np.linspace(0, 1, n)[1:]]; cur = start
    return np.array(out)


class Lab:
    """A private presentation for probing. Never touches other open presentations."""

    def __init__(self, visible=True):
        import win32com.client as wc
        self.app = wc.Dispatch("PowerPoint.Application")
        self.p = self.app.Presentations.Add(WithWindow=visible)
        self.s = self.p.Slides.Add(1, 12)
        self.tmp = os.path.join(tempfile.gettempdir(), f"warplab_{os.getpid()}.pptx")
        self.n = 0

    def close(self):
        self.p.Saved = True
        self.p.Close()

    def textbox(self, text, font="Segoe UI Symbol", size=72, box=(100, 100, 288, 288), ea=True):
        L, T, W, H = box
        tb = self.s.Shapes.AddTextbox(1, L, T, W, H)
        self.n += 1
        tb.Name = f"TB{self.n}"
        tf = tb.TextFrame2
        tf.AutoSize = 0
        tf.WordWrap = 0
        for m in ("MarginLeft", "MarginRight", "MarginTop", "MarginBottom"):
            setattr(tf, m, 0)
        tf.TextRange.Text = text
        tf.TextRange.Font.Name = font
        if ea:
            tf.TextRange.Font.NameFarEast = font
        tf.TextRange.Font.Size = size
        tb.Left, tb.Top, tb.Width, tb.Height = L, T, W, H
        return tb

    def bake(self, shape, flat=False, warp=None, adj=None):
        """Return the outline subpaths (list of command lists) of `shape`'s text."""
        d = shape.Duplicate()(1)
        d.Name = "DUP"
        d.Left, d.Top = shape.Left, shape.Top
        if flat:
            d.TextFrame2.WarpFormat = 0
        elif warp is not None:
            d.TextFrame2.WarpFormat = WARP_ID.get(warp, warp)
        if adj:
            for i, val in adj.items():
                d.Adjustments.Item[i] = val
        dm = self.s.Shapes.AddShape(1, 0, 0, 2, 2)
        dm.Name = "DMY"
        self.s.Shapes.Range(["DUP", "DMY"]).MergeShapes(2, dm)
        out = self.s.Shapes(self.s.Shapes.Count)
        out.Name = "BAKED"
        if os.path.exists(self.tmp): os.remove(self.tmp)
        self.p.SaveCopyAs(self.tmp)
        x = zipfile.ZipFile(self.tmp).read("ppt/slides/slide1.xml").decode()
        xs = [m.group(0) for m in re.finditer(r"<p:sp>.*?</p:sp>", x, re.S) if 'name="BAKED"' in m.group(0)][0]
        out.Delete()
        subs = []
        for sub in _parse_geom(xs):
            pts = nodes(sub)
            if pts[:, 0].max() < 3 and pts[:, 1].max() < 3: continue  # dummy
            subs.append(sub)
        return subs

    def slide_xml(self):
        if os.path.exists(self.tmp): os.remove(self.tmp)
        self.p.SaveCopyAs(self.tmp)
        return zipfile.ZipFile(self.tmp).read("ppt/slides/slide1.xml").decode()


# ---------------------------------------------------------------- model fitting
def inkbox(subs):
    P = np.vstack([dense(s, 20) for s in subs])
    return P[:, 0].min(), P[:, 1].min(), P[:, 0].max(), P[:, 1].max()


def corners(sub, tol_deg=20):
    """Polygon corners of a flat (straight-edged) subpath: nodes where direction turns."""
    P = nodes(sub)
    if len(P) > 1 and np.allclose(P[0], P[-1]): P = P[:-1]
    out = []
    for i in range(len(P)):
        a, b, c = P[i - 1], P[i], P[(i + 1) % len(P)]
        d1, d2 = b - a, c - b
        if np.hypot(*d1) < 1e-6 or np.hypot(*d2) < 1e-6: continue
        ang = math.degrees(abs(math.atan2(d1[0] * d2[1] - d1[1] * d2[0], d1 @ d2)))
        if ang > tol_deg: out.append(b)
    return np.array(out)


def model_fn(prst, box, ink, mode="param", adj=None, pair=(0, 1)):
    L, T, W, H = box
    ps = paths(prst, W, H, adj, L, T)
    gt, gb = Guide(ps[pair[0]]), Guide(ps[pair[1]])
    x0, y0, x1, y1 = ink

    def F(p):
        u = (p[0] - x0) / (x1 - x0)
        v = (p[1] - y0) / (y1 - y0)
        return warp_point(gt, gb, u, v, mode)
    return F


def score(F, flat, warped):
    """corner error: each flat corner's image vs nearest warped node;
    edge error: images of densely sampled flat outline vs warped dense outline (both ways)."""
    from scipy.spatial import cKDTree
    WN = np.vstack([nodes(s) for s in warped])
    WD = np.vstack([dense(s, 60) for s in warped])
    C = np.vstack([c for c in (corners(s) for s in flat) if len(c)]) if flat else np.zeros((0, 2))
    FC = np.array([F(c) for c in C]) if len(C) else np.zeros((0, 2))
    cerr = cKDTree(WN).query(FC)[0] if len(FC) else np.array([np.nan])
    FD = np.array([F(p) for p in np.vstack([dense(s, 30) for s in flat])])
    e1 = cKDTree(WD).query(FD)[0]
    e2 = cKDTree(FD).query(WD)[0]
    return dict(corner_max=float(np.max(cerr)), corner_rms=float(np.sqrt(np.mean(cerr ** 2))),
                edge_max=float(max(e1.max(), e2.max())), edge_rms=float(np.sqrt(np.mean(e1 ** 2))),
                ncorner=len(C))


def xml_edit_reopen(lab, edit):
    """Observation helper: save lab's presentation, apply `edit(slide_xml) -> slide_xml` to the
    file, and reopen it (windowless) in place of the old one. Used only to *observe* states
    (handle values, Follow Path presets) that COM cannot set; UI reachability is separate."""
    import shutil
    src = os.path.join(tempfile.gettempdir(), f"warplab_edit_{os.getpid()}.pptx")
    dst = src.replace(".pptx", "_2.pptx")
    for f in (src, dst):
        if os.path.exists(f): os.remove(f)
    lab.p.SaveCopyAs(src)
    zin = zipfile.ZipFile(src)
    zout = zipfile.ZipFile(dst, "w", zipfile.ZIP_DEFLATED)
    for it in zin.infolist():
        data = zin.read(it.filename)
        if it.filename == "ppt/slides/slide1.xml":
            data = edit(data.decode()).encode()
        zout.writestr(it, data)
    zout.close(); zin.close()
    lab.p.Saved = True; lab.p.Close()
    lab.p = lab.app.Presentations.Open(dst, WithWindow=True)
    lab.s = lab.p.Slides(1)
    return lab


def set_warp_xml(prst, adj=None, name=None):
    """Return an edit function setting every (or the named shape's) prstTxWarp."""
    av = "<a:avLst/>" if not adj else "<a:avLst>" + "".join(
        f'<a:gd name="{k}" fmla="val {v}"/>' for k, v in adj.items()) + "</a:avLst>"
    new = f'<a:prstTxWarp prst="{prst}">{av}</a:prstTxWarp>'

    def edit(x):
        if "<a:prstTxWarp" in x:
            return re.sub(r'<a:prstTxWarp prst="\w+"\s*(/>|>.*?</a:prstTxWarp>)', new, x, flags=re.S)
        # no warp yet: prstTxWarp is the first child of bodyPr in the schema
        return re.sub(r'(<a:bodyPr\b[^>]*?)(/>|>)',
                      lambda m: m.group(1) + ">" + new + ("</a:bodyPr>" if m.group(2) == "/>" else ""),
                      x, count=1)
    return edit
