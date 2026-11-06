"""R1c step 1: arc-length 1-form of A.(x,sin x), its pole structure at infinity.

Verifies:
  (1) speed^2 = q0 + q1 cos x + q2 cos^2 x for A = [[a,b],[c,d]], q0=a^2+c^2,
      q1=2(ab+cd), q2=b^2+d^2.
  (2) ds = -Q(w)/y dw with w=cos x, Q=q0+q1 w+q2 w^2, y=sqrt((1-w^2)Q).
  (3) leading behaviour at w=infinity (u=1/w):
        Q(w)/y dw = -(1/(s i sqrt(q2))) [ q2 u^-2 + (q1/2) u^-1 + O(1) ] du
      so residue at infinity = -q1/(2 s i sqrt(q2))  (nonzero iff q1 != 0),
      and a genuine double pole with coefficient q2 != 0 always.
  (4) the u^-2 term is exact (d(1/u)), i.e. a boundary term; it can never vanish.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 40


def check_speed(a, b, c, d, x):
    A = sp.Matrix([[a, b], [c, d]])
    g = sp.Matrix([x, sp.sin(x)])
    v = sp.diff(g, x)
    spd2 = sp.simplify((A * v).dot(A * v))
    w = sp.cos(x)
    q0 = a * a + c * c
    q1 = 2 * (a * b + c * d)
    q2 = b * b + d * d
    cand = q0 + q1 * w + q2 * w ** 2
    return sp.simplify(spd2 - cand)


a, b, c, d = sp.symbols('a b c d', real=True)
x, w = sp.symbols('x w', real=True)
A = sp.Matrix([[a, b], [c, d]])
q0 = a ** 2 + c ** 2
q1 = 2 * (a * b + c * d)
q2 = b ** 2 + d ** 2

print("=== (1) speed^2 identity (symbolic) ===")
g = sp.Matrix([x, sp.sin(x)])
v = sp.diff(g, x)
spd2 = sp.simplify(sp.expand((A * v).dot(A * v)))
cand = sp.expand(q0 + q1 * sp.cos(x) + q2 * sp.cos(x) ** 2)
print("difference =", sp.simplify(spd2 - cand))

print()
print("=== (3) expansion at infinity, symbolic (u = 1/w) ===")
u = sp.symbols('u', positive=True)
Qw = q0 + q1 * w + q2 * w ** 2
Y2 = (1 - w ** 2) * Qw
# f(1/u)*u^4 and sqrt
f_u4 = sp.expand(sp.simplify(Y2.subs(w, 1 / u) * u ** 4))
print("u^4 * f(1/u) =", f_u4)
# sqrt branch: sqrt(f)= u^-2 * sqrt(f_u4); sqrt(f_u4)= i sqrt(q2) * h(u), h(0)=1
q2v = sp.symbols('q2v', positive=True)
spQ = sp.sqrt(sp.simplify(-f_u4 / q2v))  # h(u)
h = sp.series(spQ, u, 0, 2).removeO()
print("h(u) =", sp.simplify(h))
R = sp.series((sp.simplify(q2v + q1 * u + q0 * u ** 2) / h), u, 0, 2).removeO()
print("R(u) = (q2+q1 u+q0 u^2)/h(u), series =", sp.expand(R))
# Q(w)/y dw = -(1/(s i sqrt(q2))) R(u) u^-2 du
lead = sp.simplify(sp.expand(R * u ** -2))
print("R(u)*u^-2 (unexpanded, has exact u^-2):", sp.simplify(lead))

print()
print("=== numeric spot check: residue = -q1/(2 i s sqrt(q2)) ===")
import random
random.seed(1)
for (aa, bb, cc, dd) in [(1.0, 0.0, 0.0, 1.0), (1.3, 0.0, 0.0, 0.7),
                         (0.9, 0.44, -0.31, 1.27), (2.0, -1.0, 1.0, 0.5)]:
    qq1 = 2 * (aa * bb + cc * dd)
    qq2 = bb * bb + dd * dd
    if qq1 != 0.0:
        res = -qq1 / (2 * 1j * mp.sqrt(qq2))
        print(f"A diag-ish {aa,bb,cc,dd}: q1={qq1:.6f} residue={mp.nstr(res, 20)}")
    else:
        print(f"A diag-ish {aa,bb,cc,dd}: q1=0 -> residue 0 (orthogonal rows)")

print()
print("=== (4) u^-2 term is exact: d(1/u) = -u^-2 du ===")
print("d(1/u)/du =", sp.simplify(sp.diff(1 / u, u)))
