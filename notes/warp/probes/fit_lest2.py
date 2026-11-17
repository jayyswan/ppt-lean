"""L_est hypothesis: the guide is subdivided in a normalized (unit) box, where its shape is the
same for every aspect, and L_est is the sum of the real-space chords over that partition.
Search: adaptive split tests on the normalized curve with a threshold eps, plus uniform N."""
import json
import numpy as np
from scipy.integrate import quad
rows = {(r["W"], r["H"]): r["t1"] for r in json.load(open("wave_edges.json"))}
exc = {(288, 288), (576, 288), (144, 144), (576, 576), (288, 144)}
A = 0.125 * 10 / 3       # normalized dy2
cpn = np.array([[0.0, 0.0], [1/3, -A], [2/3, A], [1.0, 0.0]])
def bez(c, t): return (1-t)**3*c[0] + 3*t*(1-t)**2*c[1] + 3*t*t*(1-t)*c[2] + t**3*c[3]
def split(c):
    a = (c[0]+c[1])/2; b = (c[1]+c[2])/2; d = (c[2]+c[3])/2; e = (a+b)/2; f = (b+d)/2; m = (e+f)/2
    return np.array([c[0], a, e, m]), np.array([m, f, d, c[3]])
def partition(test, eps, c=cpn, a=0.0, b=1.0, depth=0):
    if depth >= 12 or test(c) <= eps: return [a]
    l, r = split(c); m = (a + b) / 2
    return partition(test, eps, l, a, m, depth + 1) + partition(test, eps, r, m, b, depth + 1)
def dist(c):
    d = c[3]-c[0]; ch = np.linalg.norm(d); n = np.array([-d[1], d[0]]) / (ch + 1e-300)
    return max(abs((c[1]-c[0]) @ n), abs((c[2]-c[0]) @ n))
TEST = {"dist": dist, "net-ch": lambda c: sum(np.linalg.norm(c[i+1]-c[i]) for i in range(3)) - np.linalg.norm(c[3]-c[0]),
        "ctrl-dev": lambda c: max(np.linalg.norm(c[1]-(2*c[0]+c[3])/3), np.linalg.norm(c[2]-(c[0]+2*c[3])/3))}
cases = []
for (W, H), t1 in rows.items():
    dy2 = H*0.125*10/3
    sp = lambda t: float(np.hypot(W, 3*dy2*((1-2*t)*(2*t-1)+2*t*(1-t))))
    cases.append(((W, H), quad(sp, 0, t1, limit=200)[0], np.array([[0, 0], [W/3, -dy2], [2*W/3, dy2], [W, 0]], float)))
def L_of(ts, cp):
    P = np.array([bez(cp, t) for t in list(ts) + [1.0]]); return float(np.hypot(*np.diff(P, axis=0).T).sum())
res = []
for tn, test in TEST.items():
    seen = set()
    for eps in np.geomspace(1e-5, 0.5, 800):
        ts = tuple(partition(test, eps))
        if ts in seen: continue
        seen.add(ts)
        errs = {k: L_of(ts, cp) - target for k, target, cp in cases}
        typ = max(abs(e) for k, e in errs.items() if k not in exc)
        res.append((typ, tn, len(ts), round(float(eps), 6), round(max(abs(e) for k, e in errs.items() if k in exc), 3)))
for N in range(2, 30):
    ts = tuple(np.linspace(0, 1, N + 1)[:-1]); errs = {k: L_of(ts, cp) - target for k, target, cp in cases}
    res.append((max(abs(e) for k, e in errs.items() if k not in exc), "uniform", N, None, round(max(abs(e) for k, e in errs.items() if k in exc), 3)))
res.sort()
print("(max |err| typical, test, #pieces, eps, max |err| exceptional)")
for r in res[:10]: print("  ", (round(r[0], 4),) + r[1:])
