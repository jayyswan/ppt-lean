import random, sys
from ord4 import parts, psums, evalbasis, nullspace, p, I
x=[4,4,4,4,-5,-5,-5,-5,4]
def rv():
    n=[random.randrange(p) for _ in range(8)]; n.append((-sum(n))%p); return n
dirs={"u_i set1":[1,I,p-1,p-I]+[0]*5,"u_i set2":[0]*4+[1,I,p-1,p-I,0],
      "u_-1 set1":[1,p-1,1,p-1]+[0]*5,"u_-1 set2":[0]*4+[1,p-1,1,p-1,0]}
for k in (2,4):
  for d in range(2,11):
    basis=list(parts(d)); nb=len(basis); rows=[]
    for _ in range(3*nb+15):
        ev=evalbasis(basis, psums([v%p for v in x], rv()))
        for o in range(k): rows.append([ev[j][o] for j in range(nb)])
    ns=nullspace(rows, nb)
    res={}
    for nm,u in dirs.items():
        ev=evalbasis(basis, psums([v%p for v in x], u))
        res[nm]=sum(1 for v in ns if sum(v[j]*ev[j][k] for j in range(nb))%p)
    print(f"order {k} at x54, degree {d}: dim {len(ns)}, nonzero leading form at:", res, flush=True)
