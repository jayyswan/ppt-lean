# Depth-2 parabola offset tower, R5 layer-2 matching, cubic-Bezier partner.
# K = Q[x]/q3 (totally real), worked in K (x) R = R^9 via the real roots.
import mpmath as mp
mp.mp.dps = 50
X = None

def q3_roots():
    x = mp.mpf
    A = [-9,-6,-4,-1,0,2,5,7,10]
    # coefficients of prod(x-a) + 3x^6+5x^5-2x^4+x^3+2x+1, highest first
    c = [mp.mpf(1)]
    for a in A:
        c = [c[0]] + [c[i] - a*c[i-1] for i in range(1,len(c))] + [-a*c[-1]]
    extra = {6:3,5:5,4:-2,3:1,1:2,0:1}
    n = len(c)-1
    for k,v in extra.items(): c[n-k] += v
    r = mp.polyroots(c, maxsteps=200, extraprec=200)
    r = sorted([mp.re(z) for z in r])
    return c, r

MONS = [(0,0),(1,0),(0,1),(2,0),(1,1),(0,2),(3,0),(2,1),(1,2),(0,3)]

def cubic_through(P):
    """unique cubic through 9 points: nullspace of 9x10, returned normalized"""
    M = mp.matrix([[px**i*py**j for (i,j) in MONS] for (px,py) in P])
    U,S,V = mp.svd_r(M, full_matrices=True)
    c = [V[9,k] for k in range(10)]
    return c, S

def Feval(c, x, y):
    return sum(c[k]*x**i*y**j for k,(i,j) in enumerate(MONS))
def Fgrad(c, x, y):
    fx = sum(c[k]*i*x**(i-1)*y**j for k,(i,j) in enumerate(MONS) if i>0)
    fy = sum(c[k]*j*x**i*y**(j-1) for k,(i,j) in enumerate(MONS) if j>0)
    return fx, fy

# ---- polynomial helpers (lists, low degree first)
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pmul(a,b):
    r=[mp.mpf(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def ppow(a,k):
    r=[mp.mpf(1)]
    for _ in range(k): r=pmul(r,a)
    return r
def pscale(a,s): return [s*x for x in a]
def pev(a,x): return sum(c*x**i for i,c in enumerate(a))
def pshift(a,x0):
    # a(x0+u) as poly in u
    r=[mp.mpf(0)]
    for i,c in enumerate(a): r=padd(r,pscale(ppow([x0,mp.mpf(1)],i),c))
    return r

# ---- Washington Thm 2.17: v^2 = a u^4 + b u^3 + c u^2 + d u + q^2
class QuarticW:
    def __init__(s, a,b,c,d,q):
        s.a,s.b,s.c,s.d,s.q = a,b,c,d,q
        a1=d/q; a2=c-d**2/(4*q**2); a3=2*q*b; a4=-4*q**2*a; a6=a2*a4
        s.ai=(a1,a2,a3,a4,a6)
        b2=a1**2+4*a2; b4=a1*a3+2*a4; b6=a3**2+4*a6
        s.b2=b2
        # Y^2 = x^3 + b2/4 x^2 + b4/2 x + b6/4, x = Xs - b2/12
        f=[b6/4,b4/2,b2/4,mp.mpf(1)]
        g=pshift(f,-b2/12)
        s.A=g[1]; s.B=g[0]
    def to_short(s,u,v):
        a1,a2,a3,a4,a6=s.ai; q,c,d=s.q,s.c,s.d
        x=(2*q*(v+q)+d*u)/u**2
        y=(4*q**2*(v+q)+2*q*(d*u+c*u**2)-d**2*u**2/(2*q))/u**3
        return (x+s.b2/12, y+(a1*x+a3)/2)
    def from_short(s,X,Y):
        a1,a2,a3,a4,a6=s.ai; q,c,d=s.q,s.c,s.d
        x=X-s.b2/12; y=Y-(a1*x+a3)/2
        u=(2*q*(x+c)-d**2/(2*q))/y
        v=-q+u*(u*x-d)/(2*q)
        return u,v

def jinv(A,B): return 1728*4*A**3/(4*A**3+27*B**2)

def eadd(P,Q,A):
    if P is None: return Q
    if Q is None: return P
    (x1,y1),(x2,y2)=P,Q
    if abs(x1-x2)<mp.mpf(10)**(-40)*max(1,abs(x1)):
        if abs(y1+y2)<mp.mpf(10)**(-40)*max(1,abs(y1)): return None
        l=(3*x1**2+A)/(2*y1)
    else: l=(y2-y1)/(x2-x1)
    x3=l**2-x1-x2; return (x3, l*(x1-x3)-y1)

# ---- Gamma_Q side
def gammaQ_model(Qpts, y0=mp.mpf(0)):
    c,S = cubic_through(Qpts)
    # F-point P0 on line Y=y0: cubic in X
    cx=[sum(c[k]*y0**j for k,(i,j) in enumerate(MONS) if i==e) for e in range(4)]
    rts=mp.polyroots(cx[::-1],extraprec=100)
    X0=[mp.re(z) for z in rts if abs(mp.im(z))<1e-30][0]
    P0=(X0,y0)
    # F(X0+s, y0+k s) = s*(A(k) s^2 + B(k) s + C(k)) ; coefficients in s are polys in k
    coef=[[mp.mpf(0)] for _ in range(4)]
    for kk,(i,j) in enumerate(MONS):
        # (X0+s)^i (y0+k s)^j as poly in s with poly-in-k coeffs
        px=[[mp.mpf(1)]]
        for _ in range(i): px=[padd(pscale(px[m],X0) if m<len(px) else [0], px[m-1] if m>=1 else [0]) for m in range(len(px)+1)]
        py=[[mp.mpf(1)]]
        for _ in range(j): py=[padd(pscale(py[m],y0) if m<len(py) else [0], pmul(py[m-1],[0,mp.mpf(1)]) if m>=1 else [0]) for m in range(len(py)+1)]
        for a,pa in enumerate(px):
            for b,pb in enumerate(py):
                if a+b<=3: coef[a+b]=padd(coef[a+b],pscale(pmul(pa,pb),c[kk]))
    C,B,A=coef[1],coef[2],coef[3]
    Delta=padd(pmul(B,B),pscale(pmul(A,C),-4))
    # tangent slope at P0: C(k)=0 (C linear)
    kT=-C[0]/C[1]
    Dsh=pshift(Delta,kT)+[0]*5
    q=pev(B,kT)
    W=QuarticW(Dsh[4],Dsh[3],Dsh[2],Dsh[1],q)
    pts=[]
    for (Xi,Yi) in Qpts:
        s=Xi-X0; k=(Yi-y0)/s; w=2*pev(A,k)*s+pev(B,k)
        pts.append(W.to_short(k-kT,w))
    return dict(c=c,S=S,W=W,pts=pts,P0=P0,check=max(abs(Feval(c,*p)) for p in Qpts))

# ---- D side: g(t)=4t^2-4rt+u ; quartic in mu: mu^4/4 + r mu^3 + (u-1/2) mu^2 - r mu + 1/4
def D_model(r,u):
    return QuarticW(mp.mpf(1)/4, r, u-mp.mpf(1)/2, -r, mp.mpf(1)/2)

def D_point_from_t(t, r, u, ssign=1, gsign=1):
    s1=ssign*mp.sqrt(4*t**2+1); mu=s1-2*t
    sig=gsign*mp.sqrt(4*t**2-4*r*t+u); return mu, sig*mu

def mu_to_tower(mu,w):
    t=(1/mu-mu)/4; s1=(mu+1/mu)/2; sig=w/mu; return t,s1,sig

def chol_A2(r,u):
    # B2=[[1,r],[r,u]] = L L^T ; A2 = L^{-1}
    l11=mp.mpf(1); l21=r; l22=mp.sqrt(u-r**2)
    L=mp.matrix([[l11,0],[l21,l22]]); return L**-1

def tower_P2(t,s1,sig,d1,d2,A2):
    N0=mp.matrix([-2*t,1]); P0=mp.matrix([t,t**2])
    P1=P0+d1*N0/s1
    n2=(A2.T**-1)*N0/sig
    P2=A2*P1+d2*n2
    return P2[0],P2[1]
