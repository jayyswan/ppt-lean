# X4 audit helper: find a self-intersecting cubic Bezier with small integer control points,
# then show that from the crossing the same arc-length budget can land on two different
# points (two different branches through the crossing) -> the set-vs-stroke mismatch.
import numpy as np
from itertools import product

def bez(ctrl, t):
    p1, p2, p3, p4 = [np.asarray(p, float) for p in ctrl]
    u = 1 - t
    return (u**3)*p1 + 3*(u**2)*t*p2 + 3*u*(t**2)*p3 + (t**3)*p4

def power_basis(ctrl):
    p0, p1, p2, p3 = [np.asarray(p, float) for p in ctrl]
    A = -p0 + 3*p1 - 3*p2 + p3
    B = 3*p0 - 6*p1 + 3*p2
    C = -3*p0 + 3*p1
    return A, B, C, p0

def self_intersect_params(ctrl):
    """Return (t1<t2) for the unique self-intersection, or None.
    Uses B(t1)-B(t2) = (t1-t2)(A(s^2-p)+B s+C), s=t1+t2, p=t1 t2."""
    A, B, C, _ = power_basis(ctrl)
    Ax, Ay = A; Bx, By = B; Cx, Cy = C
    denom = Ax*By - Ay*Bx
    if abs(denom) < 1e-12:
        return None
    s = (Ay*Cx - Ax*Cy) / denom
    if abs(Ax) > abs(Ay):
        p = s*s + (Bx*s + Cx)/Ax
    else:
        p = s*s + (By*s + Cy)/Ay
    disc = s*s - 4*p
    if disc <= 1e-9:
        return None
    r = np.sqrt(disc)
    t1, t2 = (s-r)/2, (s+r)/2
    if 0 < t1 < 1 and 0 < t2 < 1 and t1 < t2:
        return t1, t2
    return None

found = None
grid = range(-2, 3)
for c in product([(x, y) for x in grid for y in grid], repeat=4):
    r = self_intersect_params(c)
    if r is not None:
        # verify the two parameters really give the same point
        if np.linalg.norm(bez(c, r[0]) - bez(c, r[1])) < 1e-8:
            found = (c, r)
            break

ctrl, (t1, t2) = found
p = bez(ctrl, t1)
print("control points:", ctrl)
print("crossing at t1=%.6f, t2=%.6f, point=(%.8f, %.8f)" % (t1, t2, p[0], p[1]))

def speed(ctrl, t, h=1e-7):
    a = bez(ctrl, t+h); b = bez(ctrl, t-h)
    return np.linalg.norm(a-b) / (2*h)

def arclen(ctrl, t0, t1, n=200001):
    ts = np.linspace(t0, t1, n)
    v = np.array([speed(ctrl, t) for t in ts])
    return np.trapz(v, ts)

def endpoint_from(ctrl, tstart, tend, x, n=400001):
    ts = np.linspace(tstart, tend, n)
    v = np.array([speed(ctrl, t) for t in ts])
    dz = 0.5*(v[1:]+v[:-1])*np.diff(ts)
    cum = np.concatenate([[0], np.cumsum(dz)])
    if x >= cum[-1]:
        return bez(ctrl, ts[-1]), cum[-1]
    i = np.searchsorted(cum, x)
    return bez(ctrl, ts[i]), cum[-1]

# The two branches through the crossing: (t1 -> 1) and (t2 -> 1).
LA = arclen(ctrl, t1, 1.0)
LB = arclen(ctrl, t2, 1.0)
print("arc length crossing->end via t1-branch: %.8f" % LA)
print("arc length crossing->end via t2-branch: %.8f" % LB)

x = 0.5*min(LA, LB)
pA, totA = endpoint_from(ctrl, t1, 1.0, x)
pB, totB = endpoint_from(ctrl, t2, 1.0, x)
print("budget x=%.8f -> endpoint on t1 branch: (%.8f, %.8f)" % (x, pA[0], pA[1]))
print("budget x=%.8f -> endpoint on t2 branch: (%.8f, %.8f)" % (x, pB[0], pB[1]))
print("endpoints differ by %.8f" % np.linalg.norm(pA-pB))
