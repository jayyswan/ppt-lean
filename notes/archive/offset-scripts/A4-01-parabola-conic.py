# A4-01: rational offset of the parabola y=x^2, and the conic rational-offset question.
# [symbolic] sympy exact. Cross-checked with Wolfram in A4-07.
import sympy as sp
import mpmath as mp

t, s, d, XX, YY = sp.symbols('t s d X Y', real=True)

print("="*70)
print("PARABOLA y=x^2, offset by d")
print("="*70)
# base (t, t^2), speed sqrt(1+4t^2). Reparametrise t=(s^2-1)/(4s):
#   1+4t^2 = (s^2+1)^2/(4s^2), so speed w = (s^2+1)/(2s)  (s>0).
ts = (s**2 - 1)/(4*s)
ws = (s**2 + 1)/(2*s)
Xr = sp.simplify(ts - 2*d*ts/ws)
Yr = sp.simplify(ts**2 + d/ws)
print("X(s) =", sp.factor(sp.together(Xr)))
print("Y(s) =", sp.factor(sp.together(Yr)))

nX, dX = sp.fraction(sp.together(Xr))
nY, dY = sp.fraction(sp.together(Yr))
print("deg num/den X:", sp.degree(sp.expand(nX), s), sp.degree(sp.expand(dX), s))
print("deg num/den Y:", sp.degree(sp.expand(nY), s), sp.degree(sp.expand(dY), s))

# homogenise the parametrisation: (X:Y:Z) = (nX*dY : nY*dX : dX*dY)
P0 = sp.expand(nX*dY); P1 = sp.expand(nY*dX); P2 = sp.expand(dX*dY)
g = sp.gcd(sp.gcd(sp.Poly(P0, s), sp.Poly(P1, s)), sp.Poly(P2, s))
print("common factor of (P0,P1,P2):", sp.factor(g.as_expr()))
P0q, P1q, P2q = [sp.cancel(P/g.as_expr()) for P in (P0, P1, P2)]
print("proper parametrisation degree:", max(sp.degree(sp.expand(P), s) for P in (P0q,P1q,P2q)))

F = sp.factor(sp.resultant(nX - XX*dX, nY - YY*dY, s))
Fxy = sp.Poly(F, XX, YY)
print("implicit equation total degree:", Fxy.total_degree())
print("implicit equation (monic in X^6):")
print(sp.collect(sp.expand(F/(Fxy.coeff_monomial(XX**6))), [XX, YY]))

# 30-digit check: the parametrised point is at distance |d| from the parabola and the
# displacement is orthogonal to the velocity
mp.mp.dps = 35
dval = mp.mpf('0.6')
for sv in [mp.mpf('0.7'), mp.mpf('1.3'), mp.mpf('2.9')]:
    tv = (sv**2-1)/(4*sv); wv = (sv**2+1)/(2*sv)
    Xv = tv - 2*dval*tv/wv; Yv = tv**2 + dval/wv
    dist = mp.sqrt((Xv-tv)**2 + (Yv-tv**2)**2)
    orth = (Xv-tv) + (Yv-tv**2)*(2*tv)
    print("s=%s |dist-|d||=%.3e orth=%.3e" % (mp.nstr(sv,6), float(abs(dist-abs(dval))), float(orth)))

print()
print("="*70)
print("AFFINE IMAGE OF A PARABOLA: square roots needed")
print("="*70)
# A generic parabola is the affine image of (t,t^2). Take L=[[a,b],[c,e]] and base (t,t^2):
# L(t,t^2) = (a t + b t^2, c t + e t^2). Its speed^2 is a QUADRATIC in t:
a,b,c,e = sp.symbols('a b c e', real=True)
Qa = (a + 2*b*t)**2 + (c + 2*e*t)**2
print("speed^2(L(t,t^2)) =", sp.expand(Qa))
# rationalise the conic Y^2 = Qa(t). Leading coeff Q2 = 4(b^2+e^2); its sqrt is needed
# for the point at infinity, equivalently for the reparametrisation.
print("leading coeff =", sp.expand(Qa).coeff(t,2), " sqrt ->", sp.sqrt(4*(b**2+e**2)))
# Check: with the substitution  Y = sqrt(Q2) t + k  (line through infinity) we get rational t.
k = sp.symbols('k', real=True)
Q2 = 4*(b**2+e**2)
sol = sp.solve(sp.Eq((sp.sqrt(Q2)*t + k)**2, Qa), t)
print("t(k) =", [sp.simplify(z) for z in sol])

print()
print("="*70)
print("CONIC rational-offset question: ellipse offset rational?")
print("="*70)
u = sp.symbols('u', real=True)
aa, bb = sp.symbols('a b', positive=True)
ct = (1-u**2)/(1+u**2); st = 2*u/(1+u**2)
Q = sp.simplify((aa**2*st**2 + bb**2*ct**2) * (1+u**2)**2)
print("ellipse: (speed^2)*(1+u^2)^2 =", sp.expand(Q))
print("as quartic in u, discriminant:", sp.factor(sp.discriminant(sp.Poly(sp.expand(Q), u))))
Qab = sp.expand(Q.subs({aa:2, bb:1}))
print("a=2,b=1: Q =", Qab, " disc =", sp.factor(sp.discriminant(sp.Poly(Qab, u))))
print("  -> nonzero disc: quartic curve Y^2=Q(u) is genus 1, so the offset is NOT rational.")
Qc = sp.expand(Q.subs({aa:sp.Symbol('r', positive=True), bb:sp.Symbol('r', positive=True)}))
print("a=b (circle): Q =", sp.factor(Qc), " -> perfect square, offset rational (concentric circle).")
