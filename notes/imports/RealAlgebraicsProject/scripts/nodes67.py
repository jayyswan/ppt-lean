# S67.2: number of F_p-rational nodes of X_A = {Tr a = Tr a^3 = 0} (A unramified at p,
# Frobenius of cycle type lam on the 10 coordinates).  Nodes = balanced sign vectors
# e (five +1, five -1) up to e ~ -e; F_p-rational iff Frob(S) = S or Frob(S) = S^c.
# Usage: python3 nodes67.py [decic|nonic]
import itertools, sys
from sympy.utilities.iterables import partitions
from sympy import factorint
mode = sys.argv[1] if len(sys.argv) > 1 else 'decic'
def perm_of(lam):
    p=[];i=0
    for c in lam:
        cyc=list(range(i,i+c)); p+= [cyc[(j+1)%c] for j in range(c)]; i+=c
    return p
def count(lam):
    n=sum(lam); P=perm_of(lam); c=0
    for S in itertools.combinations(range(n),5):
        if 0 not in S: continue          # one representative of {S, S^c}
        s=set(S); im={P[i] for i in S}
        if im==s or im==set(range(n))-s: c+=1
    return c
types=[]
if mode=='decic':
    for q in partitions(10):
        lam=sorted([k for k,m in q.items() for _ in range(m)],reverse=True); types.append(tuple(lam))
else:
    for q in partitions(9):
        lam=sorted([k for k,m in q.items() for _ in range(m)],reverse=True); types.append(tuple(lam)+(1,))
for lam in types:
    c=count(lam)
    bad = 'ALL p' if c==1 else ([p for p in factorint(c-1) if p>=7] if c>1 else [])
    print(lam, c, 'problem primes >=7:', bad)
