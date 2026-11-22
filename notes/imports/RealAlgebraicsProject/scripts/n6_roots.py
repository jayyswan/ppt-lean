# Session 23: rational members of N6 (nonic F/t), real-root counts and Galois groups.
import cypari, random, sys
pari=cypari.pari
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
def member():
    while True:
        s=[random.randint(-6,6) for _ in range(3)]
        y=[random.randint(-6,6) for _ in range(4)]
        if s[0]==0 or y[3]==0: continue
        k=random.randint(2,7)*random.choice([1,-1]); 
        m=pari(f"(({k})^2-1)/(2*({k}))")  # 1+m^2 square
        y1=m*s[0]                       # so y1/s0 = m
        d=pari(f"abs({y[0]})")*pari(f"(({k})^2+1)/(2*abs({k}))")
        ys=f"({y[0]}+({y1})*t+({y[2]})*t^2+({y[3]})*t^3)"
        ss=f"({s[0]}+({s[1]})*t+({s[2]})*t^2)"
        F=pari(f"{ys}^2*deriv({ys},t)^2+({ys}^2-({d})^2)*{ss}^2")
        if pari(f"polcoef({F},0,t)")!=0: print('bad',y,s,k,pari(f'polcoef({F},0,t)')); continue
        G=pari(f"({F})/t")
        if pari(f"poldegree({G},t)")!=9: continue
        return G
def group(G,pmax=3000):
    Gi=pari(f"denominator(content({G}))*{G}/content(denominator(content({G}))*{G})")
    big=False; odd=False
    for p in pari(f"primes([3,{pmax}])"):
        if pari(f"pollead({Gi})%{p}")==0: continue
        Gp=pari(f"Mod(1,{p})*{Gi}")
        if pari(f"poldegree(gcd({Gp},deriv({Gp})))")>0: continue
        degs=[int(pari(f"poldegree({g})")) for g in pari(f"factor({Gp})[,1]")]
        if 5 in degs: big=True
        if sum(1 for e in degs if e%2==0)%2==1: odd=True
        if big and odd: return 'S9'
    return 'A9+' if big else '?'
stats={}
for i in range(int(sys.argv[2]) if len(sys.argv)>2 else 40):
    G=member()
    irr=int(pari(f"polisirreducible({G})"))
    r=int(pari(f"polsturm({G})"))
    gr=group(G) if irr else '-'
    stats.setdefault((r,irr,gr),0); stats[(r,irr,gr)]+=1
    if irr and r>=7: print(r,gr,G)
print(stats)
