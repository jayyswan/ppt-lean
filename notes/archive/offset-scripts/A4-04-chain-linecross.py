# A4-04-chain-linecross.py: exact line-crossing polynomial of the chain
# off_{d2} o L1 o off_{d1}(gamma), gamma a cubic pair.  [symbolic engine: sympy]
import sympy as sp
t,A,B,C = sp.symbols('t A B C', real=True)

# cubic pair gamma(t)
x = t**3 + 2*t**2 - t
y = t**3 - t + 1
vx, vy = sp.diff(x,t), sp.diff(y,t)

def J(u1,u2): return (-u2, u1)
def Q(u1,u2): return sp.expand(u1**2+u2**2)

# ---- length 1 (calibration): r1 = gamma + d1 Jv/w1, w1^2=|v|^2 ----
d1 = sp.Rational(1,2)
# line: A r1x + B r1y - C = a0 + a1/w1
a0_1 = sp.expand(A*x + B*y - C)
a1_1 = sp.expand(d1*(A*J(vx,vy)[0] + B*J(vx,vy)[1]))
Q1 = Q(vx,vy)
P1 = sp.expand(a0_1**2 * Q1 - a1_1**2)
print("length 1: crossing poly degree =", sp.Poly(P1,t).degree())
print("  factor degrees:", [sp.Poly(f,t).degree() for f,_ in sp.factor_list(P1)[1]])

# ---- length 2: r2 = L1 gamma + d1 (L1 Jv)/w1 + d2 (J L1 v)/w1' ----
L = sp.Matrix([[2,1],[1,3]])
d2 = sp.Rational(2,3)
gx, gy = sp.expand(L[0,0]*x+L[0,1]*y), sp.expand(L[1,0]*x+L[1,1]*y)
LJv_x = sp.expand(L[0,0]*(-vy)+L[0,1]*vx)
LJv_y = sp.expand(L[1,0]*(-vy)+L[1,1]*vx)
Lv_x  = sp.expand(L[0,0]*vx+L[0,1]*vy)
Lv_y  = sp.expand(L[1,0]*vx+L[1,1]*vy)
a0_2 = sp.expand(A*gx + B*gy - C)
a1_2 = sp.expand(d1*(A*LJv_x + B*LJv_y))
a2_2 = sp.expand(d2*(A*(-Lv_y) + B*Lv_x))     # J(Lv)_x=-Lv_y, J(Lv)_y=Lv_x
Q1p = Q(Lv_x, Lv_y)
# line: a0 + a1/w1 + a2/w1' = 0  =>  U = V w1, U=a2^2 Q1 - Q1'(a0^2 Q1 + a1^2), V=2 a0 a1 Q1'
U = sp.expand(a2_2**2 * Q1 - Q1p*(a0_2**2 * Q1 + a1_2**2))
V = sp.expand(2*a0_2*a1_2*Q1p)
P2 = sp.expand(U**2 - V**2 * Q1)
print("length 2: raw polynomial degree =", sp.Poly(P2,t).degree())
fac = sp.factor_list(P2)
for f,k in fac[1]:
    print("   factor degree %2d multiplicity %d" % (sp.Poly(f,t).degree(), k))
