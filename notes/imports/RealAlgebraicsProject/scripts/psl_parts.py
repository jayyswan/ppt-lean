import itertools
# F_8 = F_2[x]/(x^3+x+1), elements 0..7 as bit vectors
def mul(a,b):
    r=0
    for i in range(3):
        if b>>i&1: r^=a<<i
    for i in (4,3):
        if r>>i&1: r^=0b1011<<(i-3)
    return r
inv={a:next(b for b in range(1,8) if mul(a,b)==1) for a in range(1,8)}
INF=8
def mob(a,b,c,d,x):
    if x==INF: return INF if c==0 else mul(a,inv[c])
    num=mul(a,x)^b; den=mul(c,x)^d
    if den==0: return INF
    return mul(num,inv[den])
G=set()
for a,b,c,d in itertools.product(range(8),repeat=4):
    if mul(a,d)^mul(b,c): G.add(tuple(mob(a,b,c,d,x) for x in range(9)))
print("|G|",len(G))
pts=range(9); parts=set()
for A in itertools.combinations(pts,3):
    rest=[x for x in pts if x not in A]
    for B in itertools.combinations(rest,3):
        C=tuple(x for x in rest if x not in B)
        parts.add(frozenset([frozenset(A),frozenset(B),frozenset(C)]))
print("partitions",len(parts))
seen=set(); orbs=[]
for P in parts:
    if P in seen: continue
    o={frozenset(frozenset(g[x] for x in blk) for blk in P) for g in G}
    seen|=o; orbs.append(len(o))
print("PSL(2,8) orbit sizes on (3,3,3) partitions:",sorted(orbs))
