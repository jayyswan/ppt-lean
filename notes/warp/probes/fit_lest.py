"""Search adaptive Bezier-length schemes for PowerPoint's L_est (Wave: Down guide).
Each guide's subdivision tree (depth <= DMAX) is built once; a scheme = (split test, threshold,
leaf estimate). Reports schemes matching the measured L_est of the typical boxes."""
import json
import numpy as np
from scipy.integrate import quad
DMAX = 9
rows = {(r["W"], r["H"]): r["t1"] for r in json.load(open("wave_edges.json"))}
def split(c):
    a = (c[0]+c[1])/2; b = (c[1]+c[2])/2; d = (c[2]+c[3])/2; e = (a+b)/2; f = (b+d)/2; m = (e+f)/2
    return np.array([c[0], a, e, m]), np.array([m, f, d, c[3]])
def tree(c, depth=0):
    ch = float(np.linalg.norm(c[3]-c[0])); net = float(sum(np.linalg.norm(c[i+1]-c[i]) for i in range(3)))
    dvec = c[3]-c[0]; n = np.array([-dvec[1], dvec[0]]) / (ch + 1e-300)
    dist = float(max(abs((c[1]-c[0]) @ n), abs((c[2]-c[0]) @ n)))
    node = dict(ch=ch, net=net, dist=dist, kids=None)
    if depth < DMAX: node["kids"] = [tree(k, depth + 1) for k in split(c)]
    return node
LEAF = {"chord": lambda n: n["ch"], "avg": lambda n: (n["ch"]+n["net"])/2, "2c+n": lambda n: (2*n["ch"]+n["net"])/3}
TEST = {"net-ch": lambda n, L: n["net"] - n["ch"], "(net-ch)/ch": lambda n, L: (n["net"]-n["ch"])/n["ch"],
        "dist": lambda n, L: n["dist"], "dist/ch": lambda n, L: n["dist"]/n["ch"],
        "(net-ch)/L": lambda n, L: (n["net"]-n["ch"])/L, "dist/L": lambda n, L: n["dist"]/L}
def est(n, test, leaf, eps, L):
    if n["kids"] is None or test(n, L) <= eps: return leaf(n)
    return sum(est(k, test, leaf, eps, L) for k in n["kids"])
cases = []
for (W, H), t1 in rows.items():
    dy2 = H*0.125*10/3
    sp = lambda t: float(np.hypot(W, 3*dy2*((1-2*t)*(2*t-1)+2*t*(1-t))))
    L = quad(sp, 0, 1, limit=200)[0]; target = quad(sp, 0, t1, limit=200)[0]
    cases.append(((W, H), tree(np.array([[0.0, 0.0], [W/3, -dy2], [2*W/3, dy2], [W, 0.0]])), target, L))
exc = {(288, 288), (576, 288), (144, 144), (576, 576), (288, 144)}
typ = [c for c in cases if c[0] not in exc]
out = []
for tn, test in TEST.items():
    scale = 1.0 if "/" in tn else 1.0
    grid = np.geomspace(1e-6, 1.0, 600) if "/" in tn else np.geomspace(1e-4, 50.0, 600)
    for ln, leaf in LEAF.items():
        for eps in grid:
            errs = [est(t, test, leaf, eps, L) - target for _, t, target, L in typ]
            out.append((max(abs(e) for e in errs), tn, ln, float(eps)))
out.sort()
for o in out[:10]: print(round(o[0], 4), o[1:])
json.dump([o[1:] for o in out[:10]], open("fit_lest_best.json", "w"))
