# Check: Q4 is a conic bundle over P^5 from a singular line; degenerate residual conics give lines on Q4 meeting the line.
import sympy as sp, random
z = sp.symbols('z0:9'); p = lambda k: sum(zi**k for zi in z)
Q4 = 6*p(4) - p(2)**2
u = [1,1,1,0,0,0,-1,-1,-1]; w = [0,0,0,1,1,1,-1,-1,-1]
L,M,N = sp.symbols('L M N')
random.seed(3); q=[random.randint(-9,9) for _ in range(8)]; q.append(-sum(q))
sub = dict(zip(z,[L*u[i]+M*w[i]+N*q[i] for i in range(9)]))
C = sp.Poly(sp.expand(sp.expand(Q4.subs(sub))/N**2), L,M,N)
print("residual conic:", C.as_expr())
Mx = sp.hessian(C.as_expr(), (L,M,N))/2
print("discriminant nonzero (smooth conic for generic plane):", sp.simplify(Mx.det())!=0)
