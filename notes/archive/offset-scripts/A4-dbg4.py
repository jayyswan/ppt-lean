import sympy as sp
t,d,X,Y=sp.symbols('t d X Y',real=True)
x = t**3 + 2*t**2 - t
y = t**3 - t + 1
E1=sp.expand((X-x)**2+(Y-y)**2-d**2)
E2=sp.expand((X-x)*sp.diff(x,t)+(Y-y)*sp.diff(y,t))
R=sp.factor(sp.resultant(E1,E2,t))
print("parametric cubic offset degree:", sp.Poly(R,X,Y).total_degree())
print("nfactors:", len(sp.factor_list(R)[1]))
# and with d->1 (concrete)
R1=sp.factor(R.subs(d,1))
print("d=1 factors:", [sp.Poly(f,X,Y).total_degree() for f,k in sp.factor_list(R1)[1]])
