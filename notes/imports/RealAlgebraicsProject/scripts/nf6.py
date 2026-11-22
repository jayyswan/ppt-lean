# Session 23: fact 6 normal form and the rational-root nonic family N6.
import sympy as sp, random
t=sp.symbols('t'); A,B,C,d=sp.symbols('A B C d')
x=sp.Poly(sp.symbols('x0:4'),t) if False else None
xs=sp.symbols('x0:4'); ys=sp.symbols('y0:4')
x=sum(xs[i]*t**i for i in range(4)); y=sum(ys[i]*t**i for i in range(4))
xp,yp=sp.diff(x,t),sp.diff(y,t)
F_full=(A*x+B*y-C)**2*(xp**2+yp**2)-d**2*(B*xp-A*yp)**2
# rotation by (c,s) with c^2+s^2=1: new coords X = c x + s y, Y = -s x + c y
c,s_=sp.symbols('c s')
X=c*x+s_*y; Y=-s_*x+c*y
Fn=(Y-C)**2*(sp.diff(X,t)**2+sp.diff(Y,t)**2)-d**2*sp.diff(X,t)**2
# with A=-s, B=c the original line A x + B y = C is Y = C
diff=sp.expand((F_full.subs({A:-s_,B:c})-Fn).subs(c**2,1-s_**2))
print('rotation normal form exact:', sp.simplify(diff.subs(c,sp.sqrt(1-s_**2)))==0)
# Jacobian rank of N6
ss=sp.symbols('s0:3'); s=sum(ss[i]*t**i for i in range(3))
F=sp.expand(y**2*sp.diff(y,t)**2+(y**2-d**2)*s**2)
coeffs=sp.Poly(F,t).all_coeffs()
params=list(ss)+list(ys)+[d]
J=sp.Matrix([[sp.diff(cf,p) for p in params] for cf in coeffs])
for trial in range(3):
    sub={p:sp.Rational(random.randint(-9,9),random.randint(1,5)) for p in params}
    # impose F(0)=0 by solving for d^2
    print('rank full family',J.subs(sub).rank())
# family with F(0)=0: d^2 = y0^2 (1 + y1^2/s0^2)
D2=ys[0]**2*(1+ys[1]**2/ss[0]**2)
G=sp.expand(sp.cancel((y**2*sp.diff(y,t)**2+(y**2-D2)*s**2)/t))
gc=sp.Poly(sp.together(G).as_numer_denom()[0],t).all_coeffs()
den=sp.together(G).as_numer_denom()[1]
gcs=[sp.cancel(cf/den) for cf in gc]
p2=list(ss)+list(ys)
J2=sp.Matrix([[sp.diff(cf,p) for p in p2] for cf in gcs])
for trial in range(3):
    sub={p:sp.Rational(random.randint(-9,9),random.randint(1,5)) or 1 for p in p2}
    print('rank N6 (7 params, 10 coeffs):',J2.subs(sub).rank())
