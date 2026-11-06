"""A3-02: high-precision verification of an offset x offset real crossing.

Instance cf1 (d1 = d2 = 1):
  x1 = 2 t^3 - 3 t^2 + 5 t + 7,   y1 = t^3 + 4 t^2 - 2 t + 1
  x2 = 3 t^3 +   t^2 - 4 t + 2,   y2 = -t^3 + 2 t^2 + 6 t - 5
The real crossing near (t1,t2) = (1.2223118, 1.6494388) is refined to >40 digits and
the geometric side conditions are checked independently of the resultant.
"""
from mpmath import mp, mpf, sqrt, findroot, matrix
mp.dps = 60

def poly(c, t):
    return sum(mpf(a) * t**i for i, a in enumerate(c))

# coefficient lists constant-first
X1 = [7, 5, -3, 2];  Y1 = [1, -2, 4, 1]
X2 = [2, -4, 1, 3];  Y2 = [-5, 6, 2, -1]
# derivatives
DX1 = [5, -6, 6]; DY1 = [-2, 8, 3]
DX2 = [-4, 2, 9]; DY2 = [6, 4, -3]

d1 = mpf(1); d2 = mpf(1)

def P1(t):
    q = poly(DX1, t)**2 + poly(DY1, t)**2
    w = sqrt(q)
    return (poly(X1, t) - d1*poly(DY1, t)/w, poly(Y1, t) + d1*poly(DX1, t)/w)

def P2(t):
    q = poly(DX2, t)**2 + poly(DY2, t)**2
    w = sqrt(q)
    return (poly(X2, t) - d2*poly(DY2, t)/w, poly(Y2, t) + d2*poly(DX2, t)/w)

def F(t1, t2):
    p = P1(t1); q = P2(t2)
    return [p[0]-q[0], p[1]-q[1]]

seed = (mpf('1.22231179911457674'), mpf('1.64943883635326178'))
sol = findroot(F, seed, tol=mpf(10)**-55)
t1, t2 = sol[0], sol[1]
print("t1 =", mp.nstr(t1, 45))
print("t2 =", mp.nstr(t2, 45))
p = P1(t1); q = P2(t2)
print("P1 = (", mp.nstr(p[0], 45), ",", mp.nstr(p[1], 45), ")")
print("P2 = (", mp.nstr(q[0], 45), ",", mp.nstr(q[1], 45), ")")
print("P1-P2 = (", mp.nstr(p[0]-q[0], 40), ",", mp.nstr(p[1]-q[1], 40), ")")
# side conditions
g1 = (poly(X1, t1), poly(Y1, t1)); g2 = (poly(X2, t2), poly(Y2, t2))
print("|P1-gamma1| =", mp.nstr(sqrt((p[0]-g1[0])**2 + (p[1]-g1[1])**2), 40))
print("|P2-gamma2| =", mp.nstr(sqrt((q[0]-g2[0])**2 + (q[1]-g2[1])**2), 40))
perp1 = (p[0]-g1[0])*poly(DX1, t1) + (p[1]-g1[1])*poly(DY1, t1)
perp2 = (q[0]-g2[0])*poly(DX2, t2) + (q[1]-g2[1])*poly(DY2, t2)
print("normal eq 1 residual =", mp.nstr(perp1, 40))
print("normal eq 2 residual =", mp.nstr(perp2, 40))
print("speed1 =", mp.nstr(sqrt(poly(DX1, t1)**2 + poly(DY1, t1)**2), 40))
print("speed2 =", mp.nstr(sqrt(poly(DX2, t2)**2 + poly(DY2, t2)**2), 40))
