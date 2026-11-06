# Z-05: independent re-verification of A4 (chains + rational offsets).
# (1) length-2 chain line-crossing polynomial: re-derived from the geometric chain
#     r2 = L*gamma + d1*(L J v)/w1 + d2*(J L v)/w1', cleared to U^2 - V^2 Q1 = 0.
# (2) parabola-offset implicit curve x cubic Bezier: degree-18 crossing polynomial.
import sympy as sp
import mpmath as mp

mp.mp.dps = 60
t = sp.symbols('t', real=True)

# ---- (1) length-2 chain ----
x = t**3 + 2*t**2 - t
y = t**3 - t + 1
vx, vy = sp.diff(x, t), sp.diff(y, t)
d1, d2 = sp.Rational(1, 2), sp.Rational(2, 3)
A, B, C = 1, 2, sp.Rational(1, 2)
L = sp.Matrix([[2, 1], [1, 3]])
gx = sp.expand(L[0, 0] * x + L[0, 1] * y)
gy = sp.expand(L[1, 0] * x + L[1, 1] * y)
LJvx = sp.expand(L[0, 0] * (-vy) + L[0, 1] * vx)
LJvy = sp.expand(L[1, 0] * (-vy) + L[1, 1] * vx)
Lvx = sp.expand(L[0, 0] * vx + L[0, 1] * vy)
Lvy = sp.expand(L[1, 0] * vx + L[1, 1] * vy)
Q1 = sp.expand(vx**2 + vy**2)
Q1p = sp.expand(Lvx**2 + Lvy**2)
a0 = sp.expand(A * gx + B * gy - C)
a1 = sp.expand(d1 * (A * LJvx + B * LJvy))
a2 = sp.expand(d2 * (A * (-Lvy) + B * Lvx))
U = sp.expand(a2**2 * Q1 - Q1p * (a0**2 * Q1 + a1**2))
V = sp.expand(2 * a0 * a1 * Q1p)
P2 = sp.Poly(sp.expand(U**2 - V**2 * Q1), t)
print("(1) length-2 chain line-crossing: degree", P2.degree(), "(expected 28)")
print("    irreducible over Q:", P2.is_irreducible)
prim = P2.primitive()[1]
print("    leading =", prim.LC(), " constant =", prim.TC())
fl = sp.factor_list(prim.as_expr())[1]
print("    rational factor degrees:", sorted([(sp.Poly(f, t).degree(), k) for f, k in fl]))
# high-precision real roots
coeffs = [int(c) for c in prim.all_coeffs()]
mpc = [mp.mpf(c) for c in coeffs]
roots = mp.polyroots(mpc, maxsteps=400, extraprec=800)
reals = sorted([r.real for r in roots if abs(r.imag) < mp.mpf(10) ** -30])
print("    #real roots:", len(reals), " first three:", [mp.nstr(r, 32) for r in reals[:3]])
# cycle types mod primes
print("    cycle types mod primes:")
for q in [101, 103, 107, 109, 113, 127, 131, 137, 139, 149]:
    fac = sp.factor_list(prim.as_expr(), modulus=q)[1]
    degs = sorted([sp.Poly(f, t).degree() for f, k in fac for _ in range(k)], reverse=True)
    print(f"      q={q}: {degs}")

# ---- (2) parabola offset implicit x cubic Bezier ----
print()
d = sp.Rational(1, 3)
s = sp.symbols('s', real=True)
Xo = (s**2 - 1) / (4 * s) - 2 * d * (s**2 - 1) / (s**2 + 1)
Yo = ((s**2 - 1) / (4 * s))**2 + d * (2 * s) / (s**2 + 1)
nX, dX = sp.fraction(sp.together(Xo))
nY, dY = sp.fraction(sp.together(Yo))
XX, YY = sp.symbols('XX YY', real=True)
Fpo = sp.Poly(sp.expand(sp.resultant(nX - XX * dX, nY - YY * dY, s)), XX, YY)
print("(2) parabola-offset implicit total degree:", Fpo.total_degree(), "(expected 6)")
u = sp.symbols('u', real=True)
P0, P1, P2c, P3 = (0, 0), (1, 2), (-1, 1), (2, -1)
bx = (1 - u)**3 * P0[0] + 3 * (1 - u)**2 * u * P1[0] + 3 * (1 - u) * u**2 * P2c[0] + u**3 * P3[0]
by = (1 - u)**3 * P0[1] + 3 * (1 - u)**2 * u * P1[1] + 3 * (1 - u) * u**2 * P2c[1] + u**3 * P3[1]
G = sp.Poly(sp.expand(Fpo.as_expr().subs({XX: bx, YY: by})), u)
Gprim = G.primitive()[1]
print("    crossing poly degree:", G.degree(), "(expected 18) irreducible:",
      sp.Poly(Gprim, u).is_irreducible)
groots = mp.polyroots([mp.mpf(int(c)) for c in Gprim.all_coeffs()], maxsteps=400, extraprec=800)
greals = sorted([r.real for r in groots if abs(r.imag) < mp.mpf(10) ** -30])
print("    #real roots:", len(greals), [mp.nstr(r, 25) for r in greals])
