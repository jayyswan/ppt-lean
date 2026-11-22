# Session 29. Galois cycle types and max real-root count for the nodal pencil Odd + g*Even (see nodal.py).
import numpy as np, sympy as sp
O=np.array([0,-63,0,-84,0,126/5,0,-36/5,0,1.0]); E=np.array([64/5,0,576/5]+[0]*7)
# twisted form rho = i*tau
Ot=np.array([0,-63,0,84,0,126/5,0,36/5,0,1.0]); Et=np.array([64/5,0,-576/5]+[0]*7)
for name,(o,e) in {'real rho':(O,E),'imag rho':(Ot,Et)}.items():
    mx=0;best=None
    for g in np.concatenate([np.linspace(-300,300,6001),np.linspace(-3,3,6001)]):
        r=np.roots((o+g*e)[::-1]); n=np.sum(abs(r.imag)<1e-9)
        if n>mx: mx=n;best=g
    print(name,'max # real roots over g:',mx,'at g=',best)
# Galois group: Frobenius cycle types for A = Odd + g Even, g rational
X=sp.symbols('X')
Oq=X**9-sp.Rational(36,5)*X**7+sp.Rational(126,5)*X**5-84*X**3-63*X; Eq=(576*X**2+64)/sp.Integer(5)
for g in [sp.Rational(1,3),sp.Rational(7,2)]:
    A=sp.Poly(sp.expand(5*(Oq+g*Eq))*g.q,X)
    print('g=',g,'irreducible:',A.is_irreducible, 'disc squarefree part sign:', sp.sign(sp.discriminant(A)))
    types=set()
    for p in sp.primerange(7,400):
        Ap=sp.Poly(A.as_expr(),X,modulus=p)
        if Ap.degree()<9 or sp.Poly(A.as_expr(),X).discriminant()%p==0: continue
        fl=Ap.factor_list()[1]
        types.add(tuple(sorted(f.degree() for f,m in fl)))
    print('  cycle types:',sorted(types))
