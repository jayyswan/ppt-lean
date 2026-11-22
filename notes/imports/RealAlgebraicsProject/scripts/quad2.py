# Local monodromy of the nine sheets around each cell of a grid on the line c = c0 + s d in the (J1,J2)-plane.
# Usage: quad.py x0 y0 side m part nparts   (cells of a m x m grid with lower-left (x0,y0); this worker does cells part::nparts)
import numpy as np, pickle, sys, os
from bl import *
from circ import cycle_type
BASE=os.environ.get('BASE','base.pkl'); Y0, c0, d = pickle.load(open(BASE, 'rb'))
x0, y0, side, m, part, nparts = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
h = side/m

def pairs(g): return np.array([g[i]-g[j] for i in range(9) for j in range(i+1, 9)])
def loop(Y, pts, maxph=0.4):
    """Track around closed polygon pts (s-values), subdividing so pair phases move < maxph. Returns perm, D-winding."""
    G0 = gram(Y); prev = pairs(np.diag(G0)); tot = 0.0
    segs = [(pts[k], pts[k+1]) for k in range(len(pts)-1)]
    while segs:
        a, b = segs.pop(0)
        Yn = track(Y, [c0+a*d, c0+b*d], h0=0.05)
        if Yn is None:
            return None
        cur = pairs(np.diag(gram(Yn))); dph = np.angle(cur/prev)
        if np.abs(dph).max() > maxph and abs(b-a) > 1e-7:
            mid = (a+b)/2; segs = [(a, mid), (mid, b)] + segs; continue
        tot += 2*dph.sum(); prev = cur; Y = Yn
    G1 = gram(Y); sig = []
    for i in range(9):
        sig.append(int(np.argmin(np.abs(np.diag(G0)-G1[i, i]))))
    if len(set(sig)) < 9 or np.abs(G1-G0[np.ix_(sig, sig)]).max() > 1e-6:
        return None
    return sig, tot/(2*np.pi)

# reach the lower-left corner of the grid from the base point via a detour away from the axis
start = x0 + 1j*y0
Y = track(Y0, [c0, c0+(start+0.37j*side)*d, c0+start*d], h0=0.05)
cells = [(i, j) for j in range(m) for i in range(m)]  # i: x index, j: y index
res = {}
cur_s = start
for idx, (i, j) in enumerate(cells):
    if idx % nparts != part:
        continue
    ll = start + i*h + 1j*j*h
    Yc = None
    for det in [0.13j, -0.31j, 0.29, -0.23+0.41j, 0.6j, -0.6j]:
        Yc = track(Y, [c0+cur_s*d, c0+((cur_s+ll)/2+det*max(h,abs(ll-cur_s)/3))*d, c0+ll*d], h0=0.05)
        if Yc is not None: break
    if Yc is None:
        print(i, j, 'reach fail', flush=True); continue
    Y, cur_s = Yc, ll
    out = loop(Y, [ll, ll+h, ll+h+1j*h, ll+1j*h, ll])
    if out is None:   # a branch point may sit on the boundary: retry with a slightly enlarged cell
        e = 0.03*h*(1+1j)
        Ye = track(Y, [c0+ll*d, c0+(ll-e)*d], h0=0.05)
        if Ye is not None:
            out = loop(Ye, [ll-e, ll+h+e.conjugate()*0+0.03*h-0.03j*h, ll+h+0.03*h+1j*h+0.03j*h, ll-0.03*h+1j*h+0.03j*h, ll-e])
            if out is not None: print(i, j, '(enlarged cell)', flush=True)
    if out is None:
        print(i, j, 'loop fail', flush=True); res[(i, j)] = None; continue
    sig, w = out
    res[(i, j)] = (sig, w)
    ct = cycle_type(sig)
    print(i, j, 'cell %.3f%+.3fi' % (ll.real, ll.imag), 'type', ct, 'windD %.2f' % w, flush=True)
pickle.dump(res, open(BASE[:-4]+'_quad_%g_%g_%g_%d_%d.pkl' % (x0, y0, side, m, part), 'wb'))
