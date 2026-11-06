# A4-05-implicit-chain.py: exact implicit equation of the length-2 chain curve
# r2 = L1 gamma + d1 (L1 Jv)/w1 + d2 (J L1 v)/w1' ,  w1^2=Q1, w1'^2=Q1'.  [symbolic]
import sympy as sp
t, w1, w2, X, Y = sp.symbols('t w1 w2 X Y', real=True)

x = t**3 + 2*t**2 - t
y = t**3 - t + 1
vx, vy = sp.diff(x,t), sp.diff(y,t)
L = sp.Matrix([[2,1],[1,3]])
d1 = sp.Rational(1,2); d2 = sp.Rational(2,3)

gx = sp.expand(L[0,0]*x+L[0,1]*y); gy = sp.expand(L[1,0]*x+L[1,1]*y)
Jvx, Jvy = -vy, vx
a1x = sp.expand(d1*(L[0,0]*Jvx+L[0,1]*Jvy)); a1y = sp.expand(d1*(L[1,0]*Jvx+L[1,1]*Jvy))
Lvx = sp.expand(L[0,0]*vx+L[0,1]*vy); Lvy = sp.expand(L[1,0]*vx+L[1,1]*vy)
a2x = sp.expand(d2*(-Lvy)); a2y = sp.expand(d2*Lvx)
Q1 = sp.expand(vx**2+vy**2)
Q2 = sp.expand(Lvx**2+Lvy**2)

E1 = sp.expand((X-gx)*w1*w2 - a1x*w2 - a2x*w1)
E2 = sp.expand((Y-gy)*w1*w2 - a1y*w2 - a2y*w1)
E3 = sp.expand(w1**2 - Q1)
E4 = sp.expand(w2**2 - Q2)

# eliminate w1 (using E3), then w2 (using E4), then t.
R1 = sp.resultant(E1, E3, w1)
R2 = sp.resultant(E2, E3, w1)
S1 = sp.resultant(R1, E4, w2)
S2 = sp.resultant(R2, E4, w2)
print("deg S1 in t:", sp.Poly(S1,t).degree(), " deg in w2:", sp.degree(S1,w2) if S1.has(w2) else 0)
print("deg S2 in t:", sp.Poly(S2,t).degree(), " deg in w2:", sp.degree(S2,w2) if S2.has(w2) else 0)
F = sp.resultant(S1, S2, t)
print("raw implicit-degree:", sp.Poly(F, X, Y).total_degree())
fl = sp.factor_list(F)
print("factors of F (total degree, mult):")
for f,k in fl[1]:
    print("   ", sp.Poly(f,X,Y).total_degree(), k, " terms:", len(sp.Poly(f,X,Y).terms()))
