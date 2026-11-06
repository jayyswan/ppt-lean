"""A3-04: high-precision bitangent-circle (offset self-crossing) for cf1, d=2.

Gamma(t) = (2t^3-3t^2+5t+7, t^3+4t^2-2t+1).  Find (t,s), t != s, with
gamma(t)+2N(t) = gamma(s)+2N(s); report the centre (X,Y) to 40+ digits and verify
that the circle of radius 2 centred there is tangent to gamma at both parameters.
"""
from mpmath import mp, mpf, sqrt, findroot
mp.dps = 60

X1=[7,5,-3,2]; Y1=[1,-2,4,1]
DX1=[5,-6,6]; DY1=[-2,8,3]
d=mpf(2)

def poly(c,t): return sum(mpf(a)*t**i for i,a in enumerate(c))
def P(t):
    q=poly(DX1,t)**2+poly(DY1,t)**2; w=sqrt(q)
    return (poly(X1,t)-d*poly(DY1,t)/w, poly(Y1,t)+d*poly(DX1,t)/w)
def F(t,s): 
    p=P(t); q=P(s); return [p[0]-q[0], p[1]-q[1]]

sol=findroot(F,(mpf('0.599337433861'),mpf('0.047671700537')),tol=mpf(10)**-55)
t,s=sol[0],sol[1]
print("t =",mp.nstr(t,45))
print("s =",mp.nstr(s,45))
print("t-s =",mp.nstr(t-s,20))
p=P(t); q=P(s)
print("centre X =",mp.nstr(p[0],45))
print("centre Y =",mp.nstr(p[1],45))
print("residual P(t)-P(s) =",mp.nstr(p[0]-q[0],35),mp.nstr(p[1]-q[1],35))
# tangency: radius 2, and (centre - gamma) parallel to N
g1=(poly(X1,t),poly(Y1,t)); g2=(poly(X1,s),poly(Y1,s))
print("|centre-gamma(t)| =",mp.nstr(sqrt((p[0]-g1[0])**2+(p[1]-g1[1])**2),40))
print("|centre-gamma(s)| =",mp.nstr(sqrt((q[0]-g2[0])**2+(q[1]-g2[1])**2),40))
print("perp(t) =",mp.nstr((p[0]-g1[0])*poly(DX1,t)+(p[1]-g1[1])*poly(DY1,t),35))
print("perp(s) =",mp.nstr((q[0]-g2[0])*poly(DX1,s)+(q[1]-g2[1])*poly(DY1,s),35))
