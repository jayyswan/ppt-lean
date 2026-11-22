# lac71.py -- session 71: power curve y^q = x^p crossed with a cubic Bezier, in the coordinate
# c of the power curve (x, y) = (c^q, c^p): the crossing polynomial is F(c^q, c^p) / c^m, F the
# Bezier's implicit cubic. Checks (numerically, from the t-roots):
#   mode 'lac' : charpoly of c = Y(t)^(?)... computed as c_i from the crossing points; prints the
#                coefficients (which vanish) for the 4/3 patterns (2,3,none) and (3,3,one,1,1)
#   mode 'reach': hill-climb on the dials to maximise the number of real crossings (r = 7, 9 ?)
# usage: python3 lac71.py lac [seed]  |  python3 lac71.py reach <pattern> <restarts> <iters> [seed]
#   pattern: A = 4/3 with deg X = 2, deg Y = 3 (no cusp passage); B = 4/3 Bezier through the cusp
#            transversally (X = t X1, Y = t Y1, X1, Y1 quadratics); C = 4/3 with X = t X1 (deg 3),
#            Y = t Y1 (deg 2)
import sys
import numpy as np
from numpy.polynomial import polynomial as Pl

def ppow(c, k):
    r = np.array([1.0])
    for _ in range(k):
        r = Pl.polymul(r, c)
    return r

def members(pat, d):
    if pat == 'A':
        X = d[0:3]; Y = d[3:7]
        return X, Y, 0
    if pat == 'B':
        X = np.concatenate([[0], d[0:3]]); Y = np.concatenate([[0], d[3:6]])
        return X, Y, 3
    if pat == 'C':
        X = np.concatenate([[0], d[0:3]]); Y = np.concatenate([[0], d[3:5]])
        return X, Y, 3
    raise ValueError

NDIAL = {'A': 7, 'B': 6, 'C': 5}

def crossing(pat, d):
    X, Y, m = members(pat, d)
    N = Pl.polysub(ppow(Y, 3), ppow(X, 4))
    N = N[m:]
    return X, Y, np.trim_zeros(N, 'b')

def lac(seed):
    rng = np.random.default_rng(seed)
    for pat in ('A', 'B'):
        d = rng.normal(size=NDIAL[pat]) + 1j * rng.normal(size=NDIAL[pat])
        X, Y, N = crossing(pat, d)
        ts = np.roots(N[::-1])
        cs = Pl.polyval(ts, Y) / Pl.polyval(ts, X)       # c = y/x on y^3 = x^4
        chk = np.max(np.abs(Pl.polyval(ts, Y)**3 - Pl.polyval(ts, X)**4) / np.abs(Pl.polyval(ts, Y))**3)
        ch = np.poly(cs)                                  # high -> low
        ch = ch / ch[0]
        print('pattern', pat, ' deg', len(ts), ' check', '%.1e' % chk)
        for k, a in enumerate(ch):
            print('   c^%d: %.3e' % (len(ch) - 1 - k, abs(a)))
        if pat == 'B':
            p1 = np.sum(cs); p2 = np.sum(cs**2); p3 = np.sum(cs**3)
            print('   p2 - p1^2/3 = %.2e,  p3 - p1^3/9 = %.2e  (|p1| = %.2e)' % (abs(p2 - p1**2/3), abs(p3 - p1**3/9), abs(p1)))
        if pat == 'A':
            w = 1 / cs
            print('   Tr(1/c) = %.2e, Tr(1/c^2) = %.2e' % (abs(np.sum(w)), abs(np.sum(w**2))))

def nreal(pat, d):
    X, Y, N = crossing(pat, d)
    if len(N) - 1 != 9:
        return -1
    r = np.roots(N[::-1])
    sc = 1 + np.abs(r)
    return int(np.sum(np.abs(r.imag) < 1e-9 * sc))

def reach(pat, restarts, iters, seed):
    rng = np.random.default_rng(seed)
    hist = {}
    best_overall = -1
    for rs in range(restarts):
        d = rng.normal(size=NDIAL[pat]) * np.exp(rng.normal(size=NDIAL[pat]))
        cur = nreal(pat, d)
        step = 0.5
        for it in range(iters):
            d2 = d + step * rng.normal(size=len(d)) * (np.abs(d) + 0.1)
            v = nreal(pat, d2)
            if v >= cur:
                d, cur = d2, v
            if it % 200 == 199:
                step *= 0.7
        hist[cur] = hist.get(cur, 0) + 1
        if cur > best_overall:
            best_overall = cur
            best_d = d.copy()
    print('pattern', pat, 'max real crossings per restart:', dict(sorted(hist.items())))
    print('best dials:', np.array2string(best_d, precision=4))
    X, Y, N = crossing(pat, best_d)
    print('real roots t:', np.sort(np.roots(N[::-1]).real[np.abs(np.roots(N[::-1]).imag) < 1e-9]))

if __name__ == '__main__':
    if sys.argv[1] == 'lac':
        lac(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    else:
        reach(sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]) if len(sys.argv) > 5 else 1)
