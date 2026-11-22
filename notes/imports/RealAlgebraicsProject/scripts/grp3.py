# Session 29. Group-law sum of the 9 points at the tracked smooth solution (reads track_end.pkl); also p1..p7 and conic rank.
# group-law sum of the 9 points at a tracked smooth S_ord solution (track_end.pkl), 60 digits
import numpy as np, mpmath as mp, pickle, sys
mp.mp.dps=60
d,x,c2=pickle.load(open(sys.argv[1] if len(sys.argv)>1 else 'track_end.pkl','rb'))
d=mp.mpc(complex(d)); xfix=mp.mpc(complex(x[8]))
hv=lambda t:(t-d)*(t+d)*(t+1)
def Fp(xx,i):
    p=mp.mpc(1)
    for j in range(9):
        if j!=i: p*=xx[i]-xx[j]
    return p
def f(v):
    xx=list(v[:8])+[xfix]; return mp.matrix([1-v[8]*hv(xx[i])**5/Fp(xx,i)**2 for i in range(9)])
v=mp.matrix([mp.mpc(complex(t)) for t in x[:8]]+[mp.mpc(complex(c2))])
for it in range(12):
    fv=f(v); J=mp.matrix(9,9); eps=mp.mpf(10)**-35
    for k in range(9):
        w=v.copy(); w[k]+=eps; J[:,k]=(f(w)-fv)/eps
    v=v-mp.lu_solve(J,fv)
print('residual',mp.nstr(mp.norm(f(v)),3))
xx=[v[i] for i in range(8)]+[xfix]; c=mp.sqrt(v[8])
pts=[(xx[i],c*hv(xx[i])**3/Fp(xx,i)) for i in range(9)]
print('max |y^2-h|/|h|',mp.nstr(max(abs(y**2-hv(t))/abs(hv(t)) for t,y in pts),3))
a=(-d**2,-d**2,mp.mpf(1))  # y^2 = x^3 + x^2 - d^2 x - d^2
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if abs(x1-x2)<mp.mpf(10)**-40*(1+abs(x1)):
        if abs(y1+y2)<mp.mpf(10)**-40*(1+abs(y1)): return None
        lam=(3*x1**2+2*a[2]*x1+a[1])/(2*y1)
    else: lam=(y2-y1)/(x2-x1)
    x3=lam**2-a[2]-x1-x2; return (x3,-(y1+lam*(x3-x1)))
S=None
for P in pts: S=add(S,P)
print('sum Q_i =', 'O' if S is None else (mp.nstr(S[0],12),mp.nstr(S[1],12)))
if S is not None:
    print('2-torsion? |y| =',mp.nstr(abs(S[1]),5))
    T=None
    for m in range(1,13):
        T=add(T,S)
        if T is None: print('order',m); break
        if abs(T[0])>mp.mpf(10)**30: print('near O at',m)
# p1,p3,p5 on the line z_i = h^2 (1+s x)/F'
s=mp.mpf('0.3')
z=[hv(xx[i])**2*(1+s*xx[i])/Fp(xx,i) for i in range(9)]; nz=max(abs(t) for t in z)
print('p1,p3,p5,p7 rel:',[mp.nstr(abs(sum(t**m for t in z))/nz**m,3) for m in (1,3,5,7)])
# conic-rank test (E vs ordinary): rank of [1,Z^2,Za,a^2]
Z=[hv(xx[i])**2/Fp(xx,i) for i in range(9)]; A=[hv(xx[i])**2*xx[i]/Fp(xx,i) for i in range(9)]
M=np.array([[1,complex(Z[i]**2),complex(Z[i]*A[i]),complex(A[i]**2)] for i in range(9)])
print('conic-rank sv:',np.linalg.svd(M,compute_uv=False))
