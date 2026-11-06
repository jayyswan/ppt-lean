# A4-02: PH cubics (Tschirnhausen and general PH), rational offsets, PH preservation.
# [symbolic] sympy exact.
import sympy as sp

t, d, XX, YY = sp.symbols('t d X Y', real=True)

def implicit_of_rat(Xr, Yr, var=t):
    nX, dX = sp.fraction(sp.together(Xr))
    nY, dY = sp.fraction(sp.together(Yr))
    F = sp.factor(sp.resultant(sp.expand(nX - XX*dX), sp.expand(nY - YY*dY), var))
    P = sp.Poly(F, XX, YY)
    return F, P.total_degree()

def proper_degree(Xr, Yr, var=t):
    nX, dX = sp.fraction(sp.together(Xr))
    nY, dY = sp.fraction(sp.together(Yr))
    P0 = sp.expand(nX*dY); P1 = sp.expand(nY*dX); P2 = sp.expand(dX*dY)
    g = sp.gcd(sp.gcd(sp.Poly(P0,var), sp.Poly(P1,var)), sp.Poly(P2,var)).as_expr()
    P0, P1, P2 = [sp.cancel(P/g) for P in (P0,P1,P2)]
    return max(sp.degree(sp.expand(P), var) for P in (P0,P1,P2))

print("="*70)
print("TSCHIRNHAUSEN CUBIC  r(t)=(t-t^3/3, t^2), PH: (x'^2+y'^2)=(1+t^2)^2")
print("="*70)
x = t - t**3/3; y = t**2
vx = sp.diff(x,t); vy = sp.diff(y,t)
print("speed^2 =", sp.factor(vx**2+vy**2), "  square root =", sp.sqrt(sp.factor(vx**2+vy**2)))
w = 1+t**2
Xr = x - 2*d*t/w      # normal (-2t,1-t^2)/(1+t^2)
Yr = y + d*(1-t**2)/w
print("offset X(t) =", sp.factor(sp.together(Xr)))
print("offset Y(t) =", sp.factor(sp.together(Yr)))
F, deg = implicit_of_rat(Xr, Yr)
print("implicit degree =", deg)
print("proper parametrisation degree =", proper_degree(Xr, Yr))
# is the offset itself PH?  r_d' = (1-d*kappa) v,  kappa = 2/(1+t^2)^2
kappa = sp.simplify((vx*sp.diff(vy,t)-vy*sp.diff(vx,t))/(vx**2+vy**2)**sp.Rational(3,2))
print("curvature kappa =", kappa)
rdx = sp.simplify(sp.diff(Xr,t)); rdy = sp.simplify(sp.diff(Yr,t))
print("offset speed^2 =", sp.factor(sp.simplify(rdx**2+rdy**2)))
print("  is it a square? numerator/denominator factor:")
print("   num:", sp.factor(sp.fraction(sp.together(sp.simplify(rdx**2+rdy**2)))[0]))
print("   den:", sp.factor(sp.fraction(sp.together(sp.simplify(rdx**2+rdy**2)))[1]))

print()
print("="*70)
print("GENERAL PH CUBIC: Bezier condition Delta2^2 = Delta1*Delta3")
print("="*70)
# complex control increments
z = sp.symbols('z', complex=True)
P0c = sp.symbols('p0', complex=True)
a, b = sp.symbols('a b', complex=True)
# hodograph = (a+(b-a)t)^2 ; integrate: B(t)=P0 + a^2 t + a(b-a) t^2 + (b-a)^2/3 t^3
# Bezier increments Delta1=a^2/3, Delta2=ab/3, Delta3=b^2/3
D1 = a**2/3; D2 = a*b/3; D3 = b**2/3
print("Delta2^2 - Delta1*Delta3 =", sp.simplify(sp.expand(D2**2 - D1*D3)))
# a concrete non-Tschirnhausen PH cubic: a=1, b=2+I  (ratio b/a=2+I)
I = sp.I
bb = 2+I
# r(t) = sum: P0 + a^2 t + a(b-a)t^2 + (b-a)^2/3 t^3, take a=1
xc = t + (bb-1)*t**2 + (bb-1)**2/3*t**3
Xg = sp.re(sp.expand(xc)); Yg = sp.im(sp.expand(xc))
print("example PH cubic r(t) = (", sp.expand(Xg), ",", sp.expand(Yg), ")")
vx2 = sp.diff(Xg,t); vy2 = sp.diff(Yg,t)
print("speed^2 =", sp.factor(sp.expand(vx2**2+vy2**2)), "  (a perfect square)")
w2 = 2*t**2 + 2*t + 1   # the polynomial square root (positive for all real t)
# unit normal
Xoff = sp.simplify(Xg - d*vy2/w2)
Yoff = sp.simplify(Yg + d*vx2/w2)
print("offset rational? denominators:", sp.fraction(sp.together(Xoff))[1])
Fg, degg = implicit_of_rat(Xoff, Yoff)
print("non-Tschirnhausen PH cubic offset implicit degree =", degg)
print("  proper param degree =", proper_degree(Xoff, Yoff))

print()
print("="*70)
print("AFFINE IMAGE OF AN OFFSET PH CUBIC: when is it PH again?")
print("="*70)
# r_d'(t) = (1-d*kappa) v(t) with v=(1-t^2,2t) up to factor; so
# |L r_d'|^2 is a square iff |L(1-t^2,2t)|^2 is a square (the rational prefactor is a square).
aa,bb2,cc,ee = sp.symbols('a b c e', real=True)
vx3 = 1-t**2; vy3 = 2*t
Lx = aa*vx3 + bb2*vy3; Ly = cc*vx3 + ee*vy3
Q4 = sp.expand(Lx**2 + Ly**2)
print("|L(1-t^2,2t)|^2 =", Q4)
# ask when this quartic is a perfect square of a quadratic (p t^2+q t+r)
p,q,r = sp.symbols('p q r', real=True)
sq = sp.expand((p*t**2+q*t+r)**2)
eqs = [sp.expand(sq - Q4).coeff(t,k) for k in range(5)]
sol = sp.solve(eqs, [p,q,r], dict=True)
print("solutions for perfect square:", sol)
# Similarity L: c=-b2, e=a  (rotation*scale) should be a solution family
sim = sp.simplify(Q4.subs({cc:-bb2, ee:aa}))
print("with L a similarity (c=-b,e=a): Q4 =", sp.factor(sim))
