# Phase 1, question 1: verify the norm-form reformulation symbolically, including
# non-invertible cases.  Claims tagged [symbolic].
#
# Correct convention (Offset.lean, offsetCrossPoly_normalForm):
#   u    = monic cubic  t^3 + a t^2 + b t + c
#   vq   = quadratic    p t^2 + q t + r        (THIS is v', the derivative of the
#                                              underlying cubic pair coordinate)
#   up   = u'  = 3t^2 + 2at + b
#   S    = up^2 + vq^2
#   W    = u^2 * S - Delta * vq^2
import sympy as sp

t, a, b, c, p, q, r, D = sp.symbols('t a b c p q r D', real=True)

f = t**7 - 14*t**5 + 49*t**3 - 36*t + 1

u = t**3 + a*t**2 + b*t + c
vq = p*t**2 + q*t + r
up = sp.diff(u, t)
S = up**2 + vq**2

W = sp.expand(u**2 * S - D * vq**2)          # Delta = D (linear; may take D>0)
print("W degree:", sp.degree(W, t))
print("Wmod degree:", sp.degree(sp.rem(sp.Poly(W, t), sp.Poly(f, t)), t))

# Identity 1:  W = u^2 u'^2 - (D - u^2) vq^2
lhs = sp.expand(u**2 * up**2 - (D - u**2) * vq**2)
print("W == u^2 u'^2 - (D-u^2)v'^2 ?", sp.expand(W - lhs) == 0)

# Identity 2: norm structure in the quadratic extension A[sqrt(S)]:
#   W = (u sqrt(S) - sqrt(D) v')(u sqrt(S) + sqrt(D) v')
norm = sp.expand((u*sp.sqrt(S) - sp.sqrt(D)*vq) * (u*sp.sqrt(S) + sp.sqrt(D)*vq))
print("norm == W ?", sp.expand(norm - W) == 0)

# Identity 3: covering W ≡ 0 (mod f) <=> (D - u^2) v'^2 = u^2 u'^2 (mod f).
print("-( (D-u^2)v'^2 - u^2u'^2 ) == W ?",
      sp.expand(-((D - u**2) * vq**2 - u**2 * up**2) - W) == 0)

# Where D - u^2 is invertible in A: v'^2 = u^2 u'^2 / (D - u^2) in A.
c_el = sp.cancel(u**2 * up**2 / (D - u**2))
print("c := u^2u'^2/(D-u^2);  c - v'^2 == W/(D-u^2) ?",
      sp.expand(sp.together(c_el - vq**2 - W/(D - u**2))) == 0)

# Non-invertible case: at a root tau with D = u(tau)^2, W(tau) = u(tau)^2 u'(tau)^2,
# so the covering equation forces u(tau) u'(tau) = 0 (over a field).
tau = sp.symbols('tau')
utau = u.subs(t, tau)
cond0 = sp.expand(W.subs(t, tau).subs(D, utau**2))
print("at D=u(tau)^2, W(tau) == u(tau)^2 u'(tau)^2 ?",
      sp.expand(cond0 - utau**2 * up.subs(t, tau)**2) == 0)
print()
print("All symbolic identities verified (correct convention).")
