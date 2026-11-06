# A4-06-degree-modp.py: implicit degree of the offset-and-affine chain, over GF(p).
# All 2^n sign branches are sampled so the full (two-sided) curve is seen, not one branch.
# [exact mod p = 2^61-1]
import random, itertools
p=(1<<61)-1

def mm(A,B):
    a,b,c,d=A; e,f,g,h=B
    return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)
def mv(A,u): return ((A[0]*u[0]+A[1]*u[1])%p,(A[2]*u[0]+A[3]*u[1])%p)
def inv2(A):
    a,b,c,d=A; det=(a*d-b*c)%p; di=pow(det,p-2,p)
    return ((d*di)%p,(-b*di)%p,(-c*di)%p,(a*di)%p)
Maps=[(2,1,1,3),(3,-1,2,1),(2,-1,1,2)]
Ds=[pow(2,p-2,p),(2*pow(3,p-2,p))%p,(2*pow(5,p-2,p))%p]
def v(t): return ((3*t*t+4*t-1)%p,(3*t*t-1)%p)
def gam(t): return ((pow(t,3,p)+2*t*t-t)%p,(pow(t,3,p)-t+1)%p)
def J(u): return ((-u[1])%p,u[0]%p)

def chain_pt(n,t,signs):
    P=[(1,0,0,1)]
    for k in range(n): P.append(mm(Maps[k],P[k]))
    g=gam(t); r=list(mv(P[n],g))
    for k in range(1,n+1):
        Pk=P[k-1]; w=mv(Pk,v(t)); Q=(w[0]*w[0]+w[1]*w[1])%p
        qi=pow(Q,(p+1)//4,p)
        if signs[k-1]==-1: qi=(-qi)%p
        C=mm(P[n],inv2(Pk)); Jw=J(w); t1,t2=mv(C,Jw)
        r[0]=(r[0]+Ds[k-1]*t1%p*qi)%p; r[1]=(r[1]+Ds[k-1]*t2%p*qi)%p
    return tuple(r)

def collect(n,want):
    pts=[]; tries=0
    while len(pts)<want and tries<200000:
        tries+=1
        t=random.randrange(2,p-1)
        Pk=(1,0,0,1); ok=True
        for k in range(n):
            wv=mv(Pk,v(t)); Q=(wv[0]*wv[0]+wv[1]*wv[1])%p
            if pow(Q,(p-1)//2,p)!=1: ok=False; break
            Pk=mm(Maps[k],Pk)
        if not ok: continue
        for signs in itertools.product([1,-1],repeat=n):
            pts.append(chain_pt(n,t,signs))
    return pts

def rank_mod_p(rows,ncols):
    M=[list(row) for row in rows]; r=0
    for c in range(ncols):
        piv=next((i for i in range(r,len(M)) if M[i][c]%p),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        inv=pow(M[r][c],p-2,p); M[r]=[(z*inv)%p for z in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%p:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(ncols)]
        r+=1
        if r==len(M): break
    return r

for n in (1,2,3):
    pts=collect(n,200)
    found=None
    for N in range(1,45):
        mons=[(i,j) for i in range(N+1) for j in range(N+1-i)]
        if len(mons)>=len(pts): break
        A=[[ (pow(pts[k][0],i,p)*pow(pts[k][1],j,p))%p for (i,j) in mons] for k in range(len(pts))]
        if rank_mod_p(A,len(mons))<len(mons): found=N; break
    print("chain n=%d : full (all-branch) implicit degree = %s  (#samples %d)"%(n,found,len(pts)))
