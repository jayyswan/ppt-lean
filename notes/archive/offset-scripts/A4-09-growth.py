# A4-09-growth.py: (a) exact length-3 line-crossing degree via the norm recursion;
# (b) implicit degree of the length-2 chain curve (distinct intersection points);
# (c) Jacobian rank (effective dimension) of the length-2 family.  [symbolic + numeric]
import sympy as sp
import numpy as np

t = sp.symbols('t', real=True)
print("="*70)
print("(a) exact crossing degrees by the norm recursion")
print("="*70)
import random
def degs(Nseed):
    random.seed(Nseed)
    R=lambda: sp.Rational(random.randint(-9,9), random.randint(1,9))
    a0 = sum(R()*t**i for i in range(4))
    a1 = sum(R()*t**i for i in range(3))
    a2 = sum(R()*t**i for i in range(3))
    a3 = sum(R()*t**i for i in range(3))
    Q1 = sum(R()*t**i for i in range(5))
    Q2 = sum(R()*t**i for i in range(5))
    Q3 = sum(R()*t**i for i in range(5))
    U2 = sp.expand(a2**2*Q1 - Q2*(a0**2*Q1 + a1**2)); V2 = sp.expand(2*a0*a1*Q2)
    D1 = sp.degree(sp.expand(a1**2 - Q1*a0**2), t)
    D2 = sp.degree(sp.expand(U2**2 - V2**2*Q1), t)
    W0 = sp.expand(a3**2*Q1*Q2 - Q3*Q2*(a0**2*Q1+a1**2) - Q3*a2**2*Q1)
    al = sp.expand(-4*Q3*Q2*a0*a1*(W0 + 2*Q3*a2**2*Q1))
    be = sp.expand(4*Q3**2*a2**2*Q1*Q2*(a0**2*Q1+a1**2) - W0**2 - 4*Q3**2*Q2**2*a0**2*a1**2*Q1)
    D3 = sp.degree(sp.expand(be**2 - al**2*Q1), t)
    return D1,D2,D3
for sd in (1,2,3):
    print("  seed",sd,":  D1,D2,D3 =", degs(sd))
print("  (analytic value must be 10, 28 (calibration), and D3 is the new figure)")

print()
print("="*70)
print("(b) implicit degree of the length-2 chain curve (# distinct points on a line)")
print("="*70)
src = open(r'C:\dev\Powerpoint\lean\archived files\offset-scripts\A4-07-new-numbers.py').read().split('# ---------- (2)')[0]
exec(src)   # defines P2 (sympy Poly in t), num etc.
numP = sp.Poly(sp.numer(sp.together(P2.as_expr())), t)
cf = [complex(sp.N(z,40)) for z in numP.all_coeffs()]
rts = np.roots(cf)
# for each t, compute the point on the chain curve (float), cluster
import mpmath as mp
mp.mp.dps=40
def pt(tv):
    tv=mp.mpf(tv.real)+1j*mp.mpf(tv.imag)
    # real branch formula r2 = Lg + d1 LJv/sqrt(Q1) + d2 JLv/sqrt(Q2)
    x = tv**3+2*tv**2-tv; y=tv**3-tv+1
    vx=3*tv**2+4*tv-1; vy=3*tv**2-1
    Q1=vx**2+vy**2
    Lvx=2*vx+vy; Lvy=vx+3*vy; Q2=Lvx**2+Lvy**2
    gx=2*x+y; gy=x+3*y
    X=gx + mp.mpf('0.5')*(-vy)/mp.sqrt(Q1) + mp.mpf('2')/3*(-Lvy)/mp.sqrt(Q2)
    Y=gy + mp.mpf('0.5')*(vx)/mp.sqrt(Q1) + mp.mpf('2')/3*(Lvx)/mp.sqrt(Q2)
    return complex(X),complex(Y)
pts=[pt(r) for r in rts if abs(r.imag)<1e-8*max(1,abs(r.real))]
# re-do for all complex roots to count geometric points
allpts=[pt(r) for r in rts]
# cluster with tolerance
def cluster(pts,tol=1e-6):
    cl=[]
    for p in pts:
        if not any(abs(p[0]-z[0])<tol and abs(p[1]-z[1])<tol for z in cl): cl.append(p)
    return cl
print("  #roots =",len(rts), " #real roots =", len(pts))
print("  #distinct complex points (tol 1e-6) =", len(cluster(allpts,1e-6)))

print()
print("="*70)
print("(c) Jacobian rank of the length-2 family -> effective dimension")
print("="*70)
def P2_coeffs(pr):
    x3,x2,x1,x0,y3,y2,y1,y0,L00,L01,L10,L11,d1,d2,A,B,C = pr
    def mul(P,Q): return np.convolve(P,Q)
    def add(P,Q):
        n=max(len(P),len(Q)); R=np.zeros(n,dtype=np.result_type(P,Q,np.float64))
        R[:len(P)]+=P; R[:len(Q)]+=Q; return R
    def smul(s,P): return s*np.array(P)
    # polynomials low->high
    xv=np.array([x0,x1,x2,x3]); yv=np.array([y0,y1,y2,y3])
    vx=np.array([x1,2*x2,3*x3]); vy=np.array([y1,2*y2,3*y3])
    gx=add(smul(L00,xv),smul(L01,yv)); gy=add(smul(L10,xv),smul(L11,yv))
    LJvx=add(smul(L00,-vy),smul(L01,vx)); LJvy=add(smul(L10,-vy),smul(L11,vx))
    Lvx=add(smul(L00,vx),smul(L01,vy)); Lvy=add(smul(L10,vx),smul(L11,vy))
    a0=add(add(smul(A,gx),smul(B,gy)),np.array([-C]))
    a1=smul(d1,add(smul(A,LJvx),smul(B,LJvy)))
    a2=smul(d2,add(smul(A,-Lvy),smul(B,Lvx)))
    Q1=add(mul(vx,vx),mul(vy,vy)); Q2=add(mul(Lvx,Lvx),mul(Lvy,Lvy))
    U=add(mul(mul(a2,a2),Q1), smul(-1,mul(Q2,add(mul(mul(a0,a0),Q1),mul(a1,a1)))))
    V=smul(2,mul(mul(a0,a1),Q2))
    P=add(mul(U,U), smul(-1,mul(mul(V,V),Q1)))
    return P
pr0=np.array([1.0, 2.0,-1.0,0.0,  1.0,0.0,-1.0,1.0,  2.0,1.0,1.0,3.0,  0.5,2.0/3,  1.0,2.0,0.5])
base=P2_coeffs(pr0); lead=base[-1]
def norm_coeffs(pr):
    P=P2_coeffs(pr); return (P/ (P[-1]) )[:-1]     # 28 normalized coeffs (drop leading)
Npar=len(pr0)
J=np.zeros((28,Npar))
h=1e-7
for j in range(Npar):
    dp=np.zeros(Npar,dtype=complex); dp[j]=1j*h
    val=norm_coeffs(pr0.astype(complex)+dp)
    J[:,j]=np.imag(val)/h
S=np.linalg.svd(J,compute_uv=False)
rank=int((S>S[0]*1e-6).sum())
print("  Jacobian shape", J.shape, " singular values[0..5]=", np.round(S[:6],3))
print("  rank =", rank, "   effective dim mod PGL2 = rank-3 =", rank-3)
