# A4-07-new-numbers.py: explicit new numbers + recovery gcd checks. [symbolic + numeric]
import sympy as sp
t,A,B,C = sp.symbols('t A B C', real=True)

# ---------- (1) length-2 chain line-crossing polynomial, degree 28 ----------
x = t**3 + 2*t**2 - t
y = t**3 - t + 1
vx, vy = sp.diff(x,t), sp.diff(y,t)
L = sp.Matrix([[2,1],[1,3]])
d1 = sp.Rational(1,2); d2 = sp.Rational(2,3)
gx = sp.expand(L[0,0]*x+L[0,1]*y); gy = sp.expand(L[1,0]*x+L[1,1]*y)
LJvx = sp.expand(L[0,0]*(-vy)+L[0,1]*vx); LJvy = sp.expand(L[1,0]*(-vy)+L[1,1]*vx)
Lvx  = sp.expand(L[0,0]*vx+L[0,1]*vy); Lvy  = sp.expand(L[1,0]*vx+L[1,1]*vy)
Q1 = sp.expand(vx**2+vy**2); Q1p = sp.expand(Lvx**2+Lvy**2)
Av,Bv,Cv = 1, 2, sp.Rational(1,2)
a0 = sp.expand(Av*gx+Bv*gy-Cv)
a1 = sp.expand(d1*(Av*LJvx+Bv*LJvy))
a2 = sp.expand(d2*(Av*(-Lvy)+Bv*Lvx))
U = sp.expand(a2**2*Q1 - Q1p*(a0**2*Q1+a1**2))
V = sp.expand(2*a0*a1*Q1p)
P2 = sp.expand(U**2 - V**2*Q1)
P2 = sp.Poly(sp.expand(P2), t)
print("(1) length-2 line-crossing poly: degree", P2.degree())
print("    irreducible over Q:", P2.is_irreducible)
# integer primitive form
num = sp.Poly(sp.numer(sp.together(P2.as_expr())), t)
coeffs = [sp.Integer(c) for c in num.all_coeffs()]
g = sp.gcd([abs(c) for c in coeffs if c!=0])
coeffs = [c//g for c in coeffs]
print("    leading/constant:", coeffs[0], coeffs[-1])
# real roots (numeric)
import mpmath as mp
mp.mp.dps = 40
fnum = sum(sp.Float(c,40)*t**k for k,c in enumerate(reversed(coeffs)))
roots = sp.nroots(sp.Poly(num, t), n=40, maxsteps=200)
reals = [r for r in roots if sp.im(r)==0 or abs(float(sp.im(r)))<1e-30]
print("    number of real roots (40 digit):", len(reals))
for r in reals[:6]:
    print("      root ~", sp.N(r, 30))

# cycle types mod primes (Chebotarev evidence)
print("    cycle types mod primes:")
for q in [101,103,107,109,113,127,131]:
    try:
        fl = sp.factor_list(sp.Poly(num, t, modulus=q))
        degs = sorted([sp.Poly(f,t).degree() for f,k in fl[1] for _ in range(k)], reverse=True)
        print("      q=%d : %s"%(q,degs))
    except Exception as e:
        print("      q=%d error %s"%(q,e))

# ---------- (2) degree-18 crossing: parabola offset implicit o cubic Bezier ----------
print()
print("(2) parabola-offset implicit (deg 6) composed with a cubic Bezier (deg 3)")
d = sp.Rational(1,3)
# parabola offset implicit, from A4-01 resultant:
s = sp.symbols('s', real=True)
X = (s**2-1)/(4*s) - 2*d*(s**2-1)/(s**2+1)     # offset x
Y = ((s**2-1)/(4*s))**2 + d*(2*s)/(s**2+1)      # offset y
nX,dX = sp.fraction(sp.together(X)); nY,dY = sp.fraction(sp.together(Y))
XX,YY = sp.symbols('XX YY', real=True)
Fpo = sp.resultant(nX-XX*dX, nY-YY*dY, s)
Fpo = sp.Poly(sp.expand(Fpo), XX, YY)
print("    parabola-offset implicit degree:", Fpo.total_degree())
# cubic Bezier control points (generic small rationals)
P0=(0,0); P1=(1,2); P2=(-1,1); P3=(2,-1)
u = sp.symbols('u', real=True)
bx = (1-u)**3*P0[0]+3*(1-u)**2*u*P1[0]+3*(1-u)*u**2*P2[0]+u**3*P3[0]
by = (1-u)**3*P0[1]+3*(1-u)**2*u*P1[1]+3*(1-u)*u**2*P2[1]+u**3*P3[1]
G = sp.expand(Fpo.as_expr().subs({XX:bx, YY:by}))
G = sp.Poly(sp.expand(G), u)
print("    crossing poly degree:", G.degree(), " irreducible over Q:", G.is_irreducible)
print("    factor degrees:", [sp.Poly(f,u).degree() for f,k in sp.factor_list(G.as_expr())[1]])
Gn = sp.Poly(sp.numer(sp.together(G.as_expr())), u)
uroots = sp.nroots(Gn, n=30, maxsteps=200)
ureals = [r for r in uroots if abs(float(sp.im(r)))<1e-25]
print("    real roots:", len(ureals))

# ---------- (3) recovery gcd, degree 1 ----------
print()
print("(3) recovery of the rational parameter by gcd over K(X,Y)")
tt = sp.symbols('tt', real=True)
def recovery_check(numX,denX,numY,denY, s0):
    X0 = sp.nsimplify(numX.subs(tt,s0)/denX.subs(tt,s0))
    Y0 = sp.nsimplify(numY.subs(tt,s0)/denY.subs(tt,s0))
    pX = sp.Poly(sp.expand(numX - X0*denX), tt)
    pY = sp.Poly(sp.expand(numY - Y0*denY), tt)
    gg = sp.gcd(pX,pY)
    return X0,Y0,sp.Poly(gg,tt).degree(), sp.factor(gg.as_expr()), sp.factor(gg.as_expr()/sp.LC(sp.Poly(gg,tt))*sp.LC(sp.Poly(gg,tt)))
# Tschirnhausen offset, d=3/5
dts = sp.Rational(3,5)
Xt = -tt*(6*dts+tt**4-2*tt**2-3)/(3*(tt**2+1))
Yt = (-dts*tt**2+dts+tt**4+tt**2)/(tt**2+1)
nXt,dXt = sp.fraction(sp.together(Xt)); nYt,dYt = sp.fraction(sp.together(Yt))
X0,Y0,deg,gg,_ = recovery_check(nXt,dXt,nYt,dYt, sp.Integer(2))
print("    Tschirnhausen offset: X0=%s Y0=%s  gcd degree=%d  gcd=%s"%(X0,Y0,deg,gg))
# parabola offset, d=1/3, s0=3
nXp,dXp = sp.fraction(sp.together(X)); nYp,dYp = sp.fraction(sp.together(Y))
X0,Y0,deg,gg,_ = recovery_check(nXp,dXp,nYp,dYp, sp.Integer(3))
print("    parabola offset:      X0=%s Y0=%s  gcd degree=%d  gcd=%s"%(X0,Y0,deg,gg))
