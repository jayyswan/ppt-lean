# Exact (mod p) data for the quadrilateral curve Sigma of S55.1
import random, sys
from sing import run
from setup56 import p, rand_V3, line_through, check_line
def mk(seed):
    rng=random.Random(seed)
    Q=rand_V3(rng); v1=line_through(Q,rng); v3=line_through(Q,rng)
    check_line(Q,v1); check_line(Q,v3)
    c1,c3=rng.randrange(p),rng.randrange(p)
    v1=[(v1[i]+c1*Q[i])%p for i in range(9)]; v3=[(v3[i]+c3*Q[i])%p for i in range(9)]
    lam=[rng.randrange(p) for _ in range(9)]; m=[rng.randrange(p) for _ in range(9)]
    return rng,Q,v1,v3,lam,m
def T(*vecs):
    # string for sum_i prod of entries (entries are strings)
    return "+".join("*".join(f"({v[i]})" for v in vecs) for i in range(9))
def system(Q,v1,v3,lam,m, a="a", rab=True):
    y=[f"y{i+1}" for i in range(9)]
    x1=[f"({Q[i]}+{a}*({v1[i]}))" for i in range(9)]
    x3=[f"({Q[i]}+s*({v3[i]}))" for i in range(9)]
    one=["1"]*9
    lQ=sum(lam[i]*Q[i] for i in range(9))%p; mQ=sum(m[i]*Q[i] for i in range(9))%p
    # Q in chart: Q/lQ ; m(Q/lQ)= mQ/lQ
    mq = mQ*pow(lQ,p-2,p)%p
    eqs=[T(one,y), T([str(l) for l in lam],y)+"-1",
         T(x1,y), T(y,y), T(x1,x1,y), T(x1,y,y), T(y,y,y),
         T(x3,y), T(x3,x3,y), T(x3,y,y)]
    if rab: eqs += ["u1*s-1", f"u2*({T([str(x) for x in m],y)}-({mq}))-1"]
    if rab and a=="a": eqs += ["u3*a-1"]
    return eqs
VARS="y1,y2,y3,y4,y5,y6,y7,y8,y9,s,u1,u2,u3"
if __name__=='__main__':
    seed=int(sys.argv[1]); mode=sys.argv[2]
    rng,Q,v1,v3,lam,m=mk(seed)
    if mode=='fibre':
        for k in range(int(sys.argv[3])):
            a0=rng.randrange(p)
            eqs=system(Q,v1,v3,lam,m,a=str(a0))
            sc=f"ring r={p},({VARS}),dp; option(redSB); ideal I={','.join(eqs)}; ideal G=std(I); print(vdim(G)); ideal E=eliminate(G,y1*y2*y3*y4*y5*y6*y7*y8*u1*u2); poly f=E[1]; print(deg(f)); list L=factorize(f); int i; string st=\"\"; for(i=1;i<=size(L[1]);i++){{st=st+string(deg(L[1][i]))+\"^\"+string(L[2][i])+\" \";}} print(st);"
            print(a0, run(sc).split())
def elim_script(eqs, w, extra=""):
    # NOTE: eqs must keep a symbolic (ring variable a); numeric a inside products overflows Singular ints
    return (f"ring r={p},(w,{VARS},a),dp; option(redSB); ideal I={','.join(eqs)},w-({w}); ideal G=std(I); print(vdim(G)); "
            f"ideal E=eliminate(G,y1*y2*y3*y4*y5*y6*y7*y8*y9*s*u1*u2*u3*a); poly f=E[1]; print(deg(f)); list L=factorize(f); int i; string st=\"\"; "
            f"for(i=1;i<=size(L[1]);i++){{st=st+string(deg(L[1][i]))+\"^\"+string(L[2][i])+\" \";}} print(st);" + extra)
if __name__=='__main__' and sys.argv[2]=='fibre2':
    for k in range(int(sys.argv[3])):
        a0=rng.randrange(p)
        eqs=system(Q,v1,v3,lam,m,a=str(a0))
        w="+".join(f"({rng.randrange(p)})*y{i+1}" for i in range(9))+f"+({rng.randrange(p)})*s"
        print(a0, run(elim_script(eqs,w)).split())
