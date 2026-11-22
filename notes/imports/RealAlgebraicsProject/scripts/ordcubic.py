"""Session 27: ordinary lines of L_135 and their odd plane cubic.
For a line Z + s v, the 9 points Q_i=(Z_i,v_i) lie on a unique odd cubic g = l0 + c3 = 0.
After a GL2 change with l0 -> y: t_i = y_i/x_i, w_i = x_i c(1,t_i) on w^2 = t c(t), and
the claim is w_i F'(t_i) / c(t_i)^3 = const (F = prod (t - t_i)).  Also report j of w^2 = t c(t).
usage: python3 ordcubic.py walk.npy [col]   col = 18 (b-lines, default) or 9 (a-lines)"""
import numpy as np, sys
np.set_printoptions(precision=6, suppress=True, linewidth=170)
def odd_cubic(x, y):
    A = np.stack([x, y, x**3, x*x*y, x*y*y, y**3], 1)
    s, V = np.linalg.svd(A)[1:]
    return V[-1], s
def jinv(G):   # G ascending coefficients of quartic e + d t + c t^2 + b t^3 + a t^4
    e, d, c, b, a = G
    I = 12*a*e - 3*b*d + c*c; J = 72*a*c*e + 9*b*c*d - 27*a*d*d - 27*e*b*b - 2*c**3
    return 6912 * I**3 / (4*I**3 - J*J)
def analyse(Z, v):
    k, s = odd_cubic(Z, v)
    l0 = k[:2]
    # new coords: yN = l0 . (x,y), xN = orthogonal complement
    M = np.array([[-l0[1], l0[0]], [l0[0], l0[1]]]) / np.linalg.norm(l0)  # rows: xN, yN
    xN, yN = M @ np.stack([Z, v])
    k2, s2 = odd_cubic(xN, yN)              # recompute in new coords: g = k2[1]*y + c3
    k2 = k2 / k2[1]                          # g = y + (k2[0] x ~ 0) + c3
    c = -k2[2:]                              # y = c(x,y), c = c0 x^3 + c1 x^2 y + c2 x y^2 + c3 y^3
    t = yN / xN
    cc = lambda tt: c[0] + c[1]*tt + c[2]*tt**2 + c[3]*tt**3
    w = xN * cc(t)
    Fp = np.array([np.prod(t[i] - np.delete(t, i)) for i in range(9)])
    ratio = w * Fp / cc(t)**3
    G = np.array([0, c[0], c[1], c[2], c[3]])
    return s[-2:], k2[0], ratio, jinv(G)
X = np.load(sys.argv[1]); col = int(sys.argv[2]) if len(sys.argv) > 2 else 18
for x in X[::3]:
    sv, lin, ratio, j = analyse(x[:9], x[col:col+9])
    print('cubic sv', sv, ' ratio spread', np.ptp(ratio)/abs(ratio.mean()), ' j =', round(j, 5))
