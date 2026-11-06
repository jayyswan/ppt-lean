"""
R1b steps 3 & 4: general cubic Bezier + one offset + one linear map.

r(t): cubic Bezier (control points P0..P3).  v=r' quadratic, a=r'' linear,
P0=|v|^2 (quartic), W=v x a (quadratic).
offset d then linear map A:
   r_d' = v (1 - d W / P0^{3/2})
   speed = |1 - d W/P0^{3/2}| * sqrt(P),  P=|A v|^2 (quartic).
On the elliptic curve y^2=P:  ds = R'(t) dt / y,  R' = P (P0^3 - d W)/P0^3.
First-kind differentials are (alpha+beta t)dt/y, so ds is first kind iff R' is a
polynomial of degree <= 1.  At infinity R' ~ P ~ p4 t^4 -> degree 4, never <=1.

Pole at infinity: t=1/u, ds ~ -sqrt(p4) u^{-4} du  (order-4 pole, second kind).
Cusp (v(t0)=0): W ~ (1/2)(t-t0)^2 (u x z), P0 ~ |u|^2(t-t0)^2, P ~ |Au|^2(t-t0)^2,
   so R ~ -d (u x z)/(2|u|^3 (t-t0)) and sqrt(P) ~ |Au||t-t0|  => speed FINITE.
"""
import sympy as sp
import mpmath as mpm
mpm.mp.dps = 30
t = sp.symbols('t', real=True)

# non-PH cubic Bezier
P0v = sp.Matrix([0, 0]); P1v = sp.Matrix([1, 2]); P2v = sp.Matrix([3, -1]); P3v = sp.Matrix([4, 1])
r = ((1-t)**3*P0v + 3*(1-t)**2*t*P1v + 3*(1-t)*t**2*P2v + t**3*P3v)
r = sp.Matrix([sp.expand(r[0]), sp.expand(r[1])])
v = sp.Matrix([sp.diff(r[0], t), sp.diff(r[1], t)])
a = sp.Matrix([sp.diff(v[0], t), sp.diff(v[1], t)])
P0 = sp.expand((v.T*v)[0])
W = sp.expand(v[0]*a[1] - v[1]*a[0])
print("P0(t) =", sp.expand(P0), " (quartic)")
print("W(t)  =", sp.expand(W), " (quadratic)")

d = sp.Rational(7, 20)
A = sp.Matrix([[sp.Rational(6,5), sp.Rational(1,4)],[sp.Rational(-1,3), sp.Rational(4,3)]])
Av = A*v
P = sp.expand((Av.T*Av)[0])
print("P(t)  =", sp.expand(P), " (quartic, generic nonsquare)")

# numeric speed check
An = mpm.matrix([[mpm.mpf(6)/5, mpm.mpf(1)/4],[mpm.mpf(-1)/3, mpm.mpf(4)/3]])
dv = mpm.mpf(7)/20
cf = [mpm.matrix([0,0]), mpm.matrix([1,2]), mpm.matrix([3,-1]), mpm.matrix([4,1])]
def bez(tv):
    tv=mpm.mpf(tv); s=1-tv
    return s**3*cf[0]+3*s**2*tv*cf[1]+3*s*tv**2*cf[2]+tv**3*cf[3]
def r_d(tv):
    tv=mpm.mpf(tv); vv=mpm.matrix([3*(1-tv)**2*(1-0)+6*(1-tv)*tv*(3-1)+3*tv**2*(4-3),
                                    3*(1-tv)**2*(2-0)+6*(1-tv)*tv*(-1-2)+3*tv**2*(1-(-1))])
    n=mpm.sqrt(vv[0]**2+vv[1]**2)
    return An*(bez(tv)+dv*mpm.matrix([-vv[1]/n, vv[0]/n]))
Pfun = sp.lambdify(t, P, 'mpmath'); P0fun = sp.lambdify(t, P0, 'mpmath'); Wfun = sp.lambdify(t, W, 'mpmath')
print("\nstep 3: numeric speed formula checks")
for tv in [mpm.mpf('0.2'), mpm.mpf('0.6'), mpm.mpf('1.5'), mpm.mpf('-0.8')]:
    spd = mpm.sqrt(sum(mpm.diff(lambda s: r_d(s)[i], tv)**2 for i in range(2)))
    g = 1 - dv*Wfun(tv)/P0fun(tv)**mpm.mpf(1.5)
    claim = abs(g)*mpm.sqrt(Pfun(tv))
    print(f"   t={float(tv):+.2f}  residual={mpm.nstr(spd-claim,5)}")

p4 = sp.limit(P/t**4, t, sp.oo)
print("\nstep 4: R'(t)=P(P0^3-dW)/P0^3.  At infinity P/t^4 ->", p4, "so R' ~ deg-4,")
print("        not a degree<=1 polynomial: ds is NOT first kind (has second-kind pole).")
# explicit pole order at infinity
u = sp.symbols('u', positive=True)
Pinf = sp.series(P.subs(t, 1/u)/u**4, u, 0, 1).removeO()
print("        P(1/u)*u^4 near u=0:", sp.simplify(Pinf))
print("        ds = R' dt/y ~ -(R' at inf)*u^-4 du -> order-4 pole (second kind).")

# cusp: v(0)=? find real roots of P0
print("\ncusp data: real roots of P0 on [0,1]:", [sp.N(z) for z in sp.solve(P0, t) if sp.im(z)==0])

# ---- F2 sanity: y=x^3, ds=sqrt(1+9x^4): second-kind part is EXACT (boundary) ----
x = sp.symbols('x', positive=True)
print("\nF2 recheck: ds=sqrt(1+9x^4) on y^2=1+9x^4 equals (2/3)dx/y + d[x sqrt(1+9x^4)/3]")
lhs = sp.sqrt(1+9*x**4); bound = x*sp.sqrt(1+9*x**4)/3
print("   derivative residual:",
      sp.simplify(sp.diff(bound, x) + sp.Rational(2,3)/sp.sqrt(1+9*x**4) - lhs))
