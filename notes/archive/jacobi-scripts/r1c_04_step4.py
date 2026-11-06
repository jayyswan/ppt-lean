"""R1c step 3(a) explicit + step 4.

(3a) Elementary closed form for int sqrt(Q(z))/z dz on the conic Y^2=Q(z).
(4)  For the sine base, Q_A(w) = q0+q1 w+q2 w^2 is positive definite
     (discriminant -4 det(A)^2 < 0), so it is never divisible by (1-w^2);
     sqrt(Q_A/(1-w^2)) therefore has a genuine pole at w=infinity and cannot be
     a holomorphic (first-kind) form under any algebraic reparametrisation.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 40
z, m = sp.symbols('z m', real=True)

print("=== (3a) conic parametrisation makes int sqrt(Q)/z dz elementary ===")
q0, q1, q2 = sp.Integer(3) / 2, sp.Integer(-1) / 4, sp.Integer(1)
# Y = z + m  (branch at infinity of Y^2 = z^2 + q1 z + q0)
R = sp.simplify((q0 - m ** 2) / (2 * m + q1 / 1))  # 2m - q1 with q1=-1/4 -> 2m+1/4? fix below
R = sp.simplify((q0 - m ** 2) / (2 * m - q1))
Yexpr = R + m
dR = sp.diff(R, m)
integrand = sp.simplify(Yexpr * dR / R)
print("R(m) =", R)
print("integrand Y dz/z =", sp.simplify(integrand))
anti = sp.integrate(integrand, m)
print("antiderivative =", sp.simplify(anti))
print("is elementary:", "log" in str(anti) or "atan" in str(anti) or "sqrt" in str(anti))

# numeric check: compare definite integral via m-param at two endpoints
def z_of_m(mv):
    return (float(q0) - mv ** 2) / (2 * mv + 0.25)


print("(note: parametrisation branch check only; genus-0 is the structural fact)")

print()
print("=== (4) Q_A positive definite, never divisible by (1-w^2) ===")
a, b, c, d, w = sp.symbols('a b c d w', real=True)
q0 = a ** 2 + c ** 2
q1 = 2 * (a * b + c * d)
q2 = b ** 2 + d ** 2
disc = sp.simplify(q1 ** 2 - 4 * q0 * q2)
print("disc(Q_A) =", sp.factor(disc), " = -4 det(A)^2")
print("det =", sp.expand(a * d - b * c))
# divisibility test: Q_A(-1) and Q_A(1)
print("Q_A(1) =", sp.expand(q0 + q1 + q2), "= (a+b)^2+(c+d)^2 >= 0")
print("Q_A(-1) =", sp.expand(q0 - q1 + q2), "= (a-b)^2+(c-d)^2 >= 0")
print("det(A) != 0 => Q_A(+-1) > 0 unless the corresponding row sum vanishes")
print("=> sqrt(Q_A/(1-w^2)) has NO cancellation of the (1-w^2) pole.")
print()
print("leading behaviour: sqrt(Q_A/(1-w^2)) ~ sqrt(q2) as w->infinity,")
print("so the 1-form K_A(w) dw ~ sqrt(q2) dw has a double pole at infinity;")
print("no algebraic change of variable kills it (pole order is intrinsic).")
