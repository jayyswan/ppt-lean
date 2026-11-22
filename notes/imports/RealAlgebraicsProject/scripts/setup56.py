# F_p data for the quadrilateral curve Sigma (S55.1): Q in V_3, two lines l1, l3 of V_3 through Q
import random, sys, re
from sing import run
p = 32003
def inv(x): return pow(x, p-2, p)
def ps(z,k): return sum(pow(x,k,p) for x in z) % p
def rand_V3(rng):
    while True:
        z = [rng.randrange(p) for _ in range(6)]
        s1,s2,s3 = [(-ps(z,k))%p for k in (1,2,3)]   # power sums required of last three
        e1 = s1; e2 = (e1*s1 - s2)*inv(2)%p; e3 = (e2*s1 - e1*s2 + s3)*inv(3)%p
        roots = [x for x in range(p) if (x**3 - e1*x*x + e2*x - e3)%p==0] if False else None
        # find roots via Singular-free brute: use factor by checking pow
        # cubic x^3 - e1 x^2 + e2 x - e3; find roots by gcd with x^p - x is slow in pure python? brute force p=32003 fine
        roots = [x for x in range(p) if (((x - e1)*x + e2)*x - e3) % p == 0]
        if len(roots)==3 or (len(roots)==1 and False):
            w = z+roots
            assert all(ps(w,k)==0 for k in (1,2,3))
            if len(set(w))==9: return w
def lin(c, var='v'):
    return "+".join(f"({c[i]%p})*{var}{i+1}" for i in range(9))
def line_through(Q, rng, tries=50):
    vs = ",".join(f"v{i+1}" for i in range(9))
    Q2 = [x*x%p for x in Q]
    for _ in range(tries):
        l0=[rng.randrange(p) for _ in range(9)]; l1=[rng.randrange(p) for _ in range(9)]; l2=[rng.randrange(p) for _ in range(9)]
        eqs = [lin([1]*9), lin(Q), lin(Q2), "+".join(f"v{i+1}^2" for i in range(9)),
               "+".join(f"({Q[i]})*v{i+1}^2" for i in range(9)), "+".join(f"v{i+1}^3" for i in range(9)),
               lin(l0), lin(l1)+"-1", lin(l2)]
        sc = f"ring r={p},({vs}),dp; ideal I={','.join(eqs)}; ideal G=std(I); print(vdim(G)); ideal E=eliminate(G,v1*v2*v3*v4*v5*v6*v7*v8); print(factorize(E[1],1));"
        out = run(sc)
        lines = out.split("\n")
        # find linear factors v9 - c
        cands=[]
        for ln in lines:
            ln=ln.strip()
            f=ln.rstrip(',')
            m=re.fullmatch(r"v9([+-]\d+)?", f)
            if m:
                cands.append((-int(m.group(1)))%p if m.group(1) else 0)
        for c in cands:
            sc2 = f"ring r={p},({vs}),dp; ideal I={','.join(eqs)},v9-({c}); ideal G=std(I); print(vdim(G)); for(int i=1;i<=9;i++){{print(reduce(var(i),G));}}"
            o2=[x.strip() for x in run(sc2).split("\n") if x.strip()]
            if o2[0]=='1':
                v=[int(x)%p for x in o2[1:10]]
                return v
    raise Exception("no line")
def check_line(Q,v):
    for s in range(5):
        z=[(Q[i]+s*v[i])%p for i in range(9)]
        assert all(ps(z,k)==0 for k in (1,2,3)), "line not in V3"
if __name__=='__main__':
    seed=int(sys.argv[1]); rng=random.Random(seed)
    Q=rand_V3(rng); v1=line_through(Q,rng); v3=line_through(Q,rng)
    check_line(Q,v1); check_line(Q,v3)
    # randomise base points of the parametrisations
    c1,c3=rng.randrange(p),rng.randrange(p)
    v1=[(v1[i]+c1*Q[i])%p for i in range(9)]; v3=[(v3[i]+c3*Q[i])%p for i in range(9)]
    print(Q); print(v1); print(v3)
