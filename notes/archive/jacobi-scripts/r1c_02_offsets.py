"""R1c step 2: offsets of A.(x, sin x).

(a) one offset after linear map A:  speed = sqrt(Q_A(w)) |1 + d detA sin x / Q_A^{3/2}|,
    w=cos x.  Since sin x dx = -dw, the correction is -d detA dw/Q_A: an ELEMENTARY
    (genus 0, rational-in-w) integral.  Checked symbolically (concrete rational A) and
    evaluated to 30 digits.
(b) two-offset chain: complex-step check of the F3 formula.
(c) leading sqrt(Q_n) dx is untouched -> double pole at infinity survives offsets.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 50
x = sp.symbols('x', real=True)


def un(v):
    return sp.Matrix([-v[1], v[0]]) / sp.sqrt(v.dot(v))


print("=== (a) symbolic one-offset identity, concrete rational A ===")
A = sp.Matrix([[sp.Rational(13, 10), sp.Rational(2, 5)],
               [sp.Rational(-3, 10), sp.Rational(8, 5)]])
dd = sp.Rational(37, 100)
g = sp.Matrix([x, sp.sin(x)])
v = sp.diff(g, x)
eta = A * g + dd * un(A * v)
veta = sp.diff(eta, x)
Q = sp.expand((A * v).dot(A * v))
s2 = sp.expand(veta.dot(veta))
c2 = sp.expand(Q * (1 + dd * sp.det(A) * sp.sin(x) / Q ** sp.Rational(3, 2)) ** 2)
print("speed^2 - claim^2 simplified:", sp.simplify(sp.expand(s2 - c2)))

fe = sp.lambdify(x, sp.sqrt(Q * (1 + dd * sp.det(A) * sp.sin(x) / Q ** sp.Rational(3, 2)) ** 2),
                 'mpmath')
# independent numeric speed: numeric derivative of the curve
import math


def eta_num(xv):
    xx = mp.mpf(xv)
    wv = mp.cos(xx)
    p = mp.matrix([A[0, 0] * xx + A[0, 1] * mp.sin(xx),
                   A[1, 0] * xx + A[1, 1] * mp.sin(xx)])
    vv = mp.matrix([A[0, 0] + A[0, 1] * wv, A[1, 0] + A[1, 1] * wv])
    nn = mp.matrix([-vv[1], vv[0]]) / mp.sqrt(vv[0] ** 2 + vv[1] ** 2)
    return mp.matrix([p[0] + dd * nn[0], p[1] + dd * nn[1]])


def num_speed(xv):
    return mp.sqrt(sum(d * d for d in mp.diff(lambda t: eta_num(t), mp.mpf(xv))))


for xv in ['0.3', '0.9', '1.4', '-2.1']:
    a = num_speed(xv)
    b = fe(mp.mpf(xv))
    print(f"x={xv:>6} numdiff={mp.nstr(a,25)} form={mp.nstr(b,25)} diff={mp.nstr(a-b,4)}")

print()
print("=== (a') correction is rational in w: int -dd detA dw/(1+w^2) ===")
wc = sp.symbols('wc', real=True)
print(sp.integrate(-dd * sp.det(A) / (1 + wc ** 2), wc))

print()
print("=== (b) two-offset chain: complex-step vs F3 ===")
h = mp.mpf('1e-20')


def AG(Amat, p):
    return mp.matrix([Amat[0] * p[0] + Amat[1] * p[1],
                      Amat[2] * p[0] + Amat[3] * p[1]])


A1 = [1, 0, 0, 1]
A2 = [2, 0, 0, 1]
d0 = mp.mpf('0.3')
d1 = mp.mpf('-0.2')


def r1(t):
    # curve after A1 then offset d0
    p = AG(A1, mp.matrix([t, mp.sin(t)]))
    v = AG(A1, mp.matrix([1, mp.cos(t)]))
    n = mp.matrix([-v[1], v[0]]) / mp.sqrt(v[0] ** 2 + v[1] ** 2)
    return p + d0 * n


def r3(t):
    p = AG(A2, r1(t))
    v = AG(A2, r1p(t))
    n = mp.matrix([-v[1], v[0]]) / mp.sqrt(v[0] ** 2 + v[1] ** 2)
    return p + d1 * n


def r1p(t):
    return mp.matrix([mp.diff(lambda s: r1(s)[0], t), mp.diff(lambda s: r1(s)[1], t)])


def r3p(t):
    return mp.matrix([mp.diff(lambda s: r3(s)[0], t), mp.diff(lambda s: r3(s)[1], t)])


for xv in ['0.4', '1.1', '2.3']:
    xm = mp.mpf(xv)
    spd = mp.sqrt(r3p(xm)[0] ** 2 + r3p(xm)[1] ** 2)
    w = mp.cos(xm)
    cross = -mp.sin(xm)
    Q1 = 1 + w ** 2
    Q2 = 4 + w ** 2
    pred = abs(mp.sqrt(Q2) * (1 - d0 * 1 * cross / Q1 ** mp.mpf('1.5')
                              - d1 * 2 * cross / Q2 ** mp.mpf('1.5')))
    print(f"x={xv:>5} numdiff={mp.nstr(spd,15)} F3={mp.nstr(pred,15)} diff={mp.nstr(spd-pred,3)}")
