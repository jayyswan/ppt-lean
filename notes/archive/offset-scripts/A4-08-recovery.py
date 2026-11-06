# A4-08-recovery.py: recovery of the rational parameter by gcd over K(X,Y) (degree 1).
import sympy as sp
tt = sp.symbols('tt', real=True)

def recovery_check(numX,denX,numY,denY, s0):
    X0 = sp.nsimplify(numX.subs(tt,s0)/denX.subs(tt,s0))
    Y0 = sp.nsimplify(numY.subs(tt,s0)/denY.subs(tt,s0))
    pX = sp.Poly(sp.expand(numX - X0*denX), tt)
    pY = sp.Poly(sp.expand(numY - Y0*denY), tt)
    gg = sp.gcd(pX,pY)
    return X0,Y0,sp.Poly(gg,tt).degree(), sp.factor(gg.as_expr())

# Tschirnhausen offset d=3/5
dts = sp.Rational(3,5)
Xt = -tt*(6*dts+tt**4-2*tt**2-3)/(3*(tt**2+1))
Yt = (-dts*tt**2+dts+tt**4+tt**2)/(tt**2+1)
nXt,dXt = sp.fraction(sp.together(Xt)); nYt,dYt = sp.fraction(sp.together(Yt))
print("Tschirnhausen:", recovery_check(nXt,dXt,nYt,dYt, sp.Integer(2)))

# parabola offset d=1/3, param s0=3
d = sp.Rational(1,3); s = tt
Xp = (s**2-1)/(4*s) - 2*d*(s**2-1)/(s**2+1)
Yp = ((s**2-1)/(4*s))**2 + d*(2*s)/(s**2+1)
nXp,dXp = sp.fraction(sp.together(Xp)); nYp,dYp = sp.fraction(sp.together(Yp))
print("parabola:     ", recovery_check(nXp,dXp,nYp,dYp, sp.Integer(3)))
print("parabola s0=5:", recovery_check(nXp,dXp,nYp,dYp, sp.Integer(5)))
