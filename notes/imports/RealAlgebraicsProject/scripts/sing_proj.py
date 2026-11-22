# Session 22: excess intersection of D = {Q4=Q5=0} along a singular line of Q4.
import sympy as sp, random
z = sp.symbols('z0:9')
p = lambda k: sum(zi**k for zi in z)
Q4 = 6*p(4) - p(2)**2
Q5 = 18*p(5) - 5*p(2)*p(3)
a,b = sp.symbols('a b')
# singular line for partition {012}{345}{678}: (a,a,a,b,b,b,c,c,c), c=-a-b
u = [1,1,1,0,0,0,-1,-1,-1]; w = [0,0,0,1,1,1,-1,-1,-1]
random.seed(1)
q = [random.randint(-9,9) for _ in range(8)]; q.append(-sum(q))
L,M,N = sp.symbols('L M N')
pt = [L*u[i]+M*w[i]+N*q[i] for i in range(9)]
sub = dict(zip(z,pt))
q4 = sp.Poly(sp.expand(Q4.subs(sub)), L,M,N)
q5 = sp.Poly(sp.expand(Q5.subs(sub)), L,M,N)
def nu_order(P):
    k=0
    while all(m[2]>k for m in P.monoms()): k+=1
    return k
print("order of N in Q4|plane:", nu_order(q4), " in Q5|plane:", nu_order(q5))
C = sp.expand(q4.as_expr()/N**nu_order(q4)); F = sp.expand(q5.as_expr()/N**nu_order(q5))
print("deg residual Q4:", sp.Poly(C,L,M,N).total_degree(), " deg residual Q5:", sp.Poly(F,L,M,N).total_degree())
# count intersections C=F=0 off N=0 (affine N=1) vs total
r = sp.resultant(C.subs(N,1), F.subs(N,1), M)
r = sp.Poly(r, L)
print("affine resultant degree in L:", r.degree())
# points on N=0
c0 = sp.Poly(C.subs(N,0),L,M); f0=sp.Poly(F.subs(N,0),L,M)
print("C|N=0:", sp.factor(c0.as_expr())); print("F|N=0:", sp.factor(f0.as_expr()))
print("gcd on line:", sp.gcd(c0.as_expr(), f0.as_expr()))
