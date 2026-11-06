"""
R1b step 2 (fast): PH cubic Tschirnhausen -> offset -> linear map.

r(t)=(t-t^3/3, t^2), r'=(1-t^2,2t), |r'|^2=(1+t^2)^2, W=r'xr''=2(1+t^2).
offset by d then linear map A:  r_d' = r'(1 - dW/sigma^3) = r' g,
g = ((1+t^2)^2 - 2d)/(1+t^2)^2,  speed = |g| sqrt(Q_A(r')),  ds = sqrt(P) R dt.
"""
import sympy as sp
import mpmath as mpm
mpm.mp.dps = 30

t = sp.symbols('t', real=True)
d = sp.Rational(3, 10)
A = sp.Matrix([[2, sp.Rational(1, 5)], [sp.Rational(1, 3), sp.Rational(3, 2)]])
r = sp.Matrix([t - t**3/3, t**2])
rd = sp.Matrix([sp.diff(r[0], t), sp.diff(r[1], t)])
sig2 = sp.expand((rd.T*rd)[0]); W = sp.expand(rd[0]*sp.diff(rd[1], t) - rd[1]*sp.diff(rd[0], t))
Ard = A*rd
P = sp.expand((Ard.T*Ard)[0])
g = sp.expand((sig2 - 2*d)/sig2)
print("sigma^2 =", sp.factor(sig2), " W =", sp.factor(W), " (W=2 sigma)")
print("P(t) =", sp.expand(P))
print("R(t) = (sigma^2-2d)/sigma^2, sigma^2-2d =", sp.factor(sp.numer(sp.together(g))))

An = mpm.matrix([[2, mpm.mpf(1)/5],[mpm.mpf(1)/3, mpm.mpf(3)/2]])
dv = mpm.mpf(3)/10
def vfun(tv):
    tv = mpm.mpf(tv); return mpm.matrix([1-tv**2, 2*tv])
def r_d(tv):
    tv = mpm.mpf(tv); v = vfun(tv); n = mpm.sqrt(v[0]**2+v[1]**2)
    p = mpm.matrix([tv-tv**3/3, tv**2]) + dv*mpm.matrix([-v[1]/n, v[0]/n])
    return An*p
Pfun = sp.lambdify(t, P, 'mpmath'); gfun = sp.lambdify(t, g, 'mpmath')
print("\n(i) numeric speed checks:")
for tv in [mpm.mpf('0.3'), mpm.mpf('1.4'), mpm.mpf('2.7'), mpm.mpf('-1.1')]:
    spd = mpm.sqrt(sum(mpm.diff(lambda s: r_d(s)[i], tv)**2 for i in range(2)))
    claim = abs(gfun(tv))*mpm.sqrt(Pfun(tv))
    print(f"   t={float(tv):+.2f}  residual={mpm.nstr(spd-claim,5)}")

print("\n(ii)/(iii) asymptotics:")
p4 = sp.limit(P/t**4, t, sp.oo); print("   P/t^4 ->", p4, "  R(inf) ->", sp.limit(g, t, sp.oo))
print("   so P*R ~ %s t^4 : degree 4 at infinity, NOT constant (and NOT linear)" % p4)
print("   on y^2=P, ds=(P R/y)dt; after t=1/u this is ~ u^-4 du: order-4 pole (second kind)")

print("\n(iv) depth-2 chain (offset,map,offset,map), numeric speed growth:")
B = mpm.matrix([[mpm.mpf(7)/5, -mpm.mpf(2)/7],[mpm.mpf(1)/4, mpm.mpf(9)/8]])
d2 = mpm.mpf(2)/5
def C1(tv):
    tv = mpm.mpf(tv); return An*(r_d(tv))
def C1p(tv):
    tv = mpm.mpf(tv); v = vfun(tv)
    return An*(v*(1 - dv*(2*(1+tv**2))/(1+tv**2)**3))
def C2(tv):
    tv = mpm.mpf(tv); p = C1(tv); q = C1p(tv); n = mpm.sqrt(q[0]**2+q[1]**2)
    return B*(p + d2*mpm.matrix([-q[1]/n, q[0]/n]))
for tv in [mpm.mpf('0.5'), mpm.mpf('2.0'), mpm.mpf('6.0')]:
    spd = mpm.sqrt(sum(mpm.diff(lambda s: C2(s)[i], tv)**2 for i in range(2)))
    print(f"   t={float(tv):.2f}  speed={mpm.nstr(spd,10)}   speed/t^2={mpm.nstr(spd/tv**2,6)}")
