"""A3-05: is the bitangent-circle centre degree 16?  Verify the PSLQ candidate at 200 digits.
Also try pslq again at higher precision to pin the minimal polynomial.
"""
from mpmath import mp, mpf, sqrt, findroot, pslq
mp.dps = 200

X1=[7,5,-3,2]; Y1=[1,-2,4,1]; DX1=[5,-6,6]; DY1=[-2,8,3]
d=mpf(2)
def poly(c,t): return sum(mpf(a)*t**i for i,a in enumerate(c))
def P(t):
    q=poly(DX1,t)**2+poly(DY1,t)**2; w=sqrt(q)
    return (poly(X1,t)-d*poly(DY1,t)/w, poly(Y1,t)+d*poly(DX1,t)/w)
def F(t,s):
    p=P(t); q=P(s); return [p[0]-q[0], p[1]-q[1]]
t,s=findroot(F,(mpf('0.599337433861129445'),mpf('0.0476717005369934434')),tol=mpf(10)**-190)
cx,cy=P(t)
print("X =", mp.nstr(cx,150))
print("Y =", mp.nstr(cy,150))
cand16=[-1483,-1568,1170,4090,-2792,-6641,10759,9045,-9702,2122,4647,647,3285,1580,-10370,-386,212]
val=sum(mpf(a)*cx**k for k,a in enumerate(cand16))
print("deg16 candidate at X:", mp.nstr(val, 30))
# re-run pslq at higher precision on X
for deg in (32, 16, 8, 4):
    rel=pslq([cx**k for k in range(deg+1)], tol=mpf(10)**-150, maxcoeff=10**160, maxsteps=10**6)
    print("pslq deg", deg, "->", rel)
# same for Y
for deg in (32, 16):
    rel=pslq([cy**k for k in range(deg+1)], tol=mpf(10)**-150, maxcoeff=10**160, maxsteps=10**6)
    print("pslq Y deg", deg, "->", rel)
