# For degree d: exact space of symmetric invariants vanishing to order >=4 on Pi,
# and the binary forms (in a,b) given by their normal quartic at u=(1,i,-1,-i) on 4-set 1.
import random, sys, sympy as sp
from math import comb
from ord4 import parts
random.seed(3)
a,b=sp.symbols('a b')
def mul(A,B,R=5):
    C=[0]*R
    for i,x in enumerate(A):
        for j in range(R-i): C[i+j]+=x*B[j]
    return C
def psums(x,n,expand=False):
    return {k:[(sp.expand if expand else (lambda z:z))(sum(comb(k,j)*xi**(k-j)*ni**j for xi,ni in zip(x,n)) if j<=k else 0) for j in range(5)] for k in range(2,10)}
def ev(basis,ps,expand=False):
    out=[]
    for lam in basis:
        s=[1,0,0,0,0]
        for k in lam:
            s=mul(s,ps[k])
            if expand: s=[sp.expand(z) for z in s]
        out.append(s)
    return out
def main(d,order=4,u=None):
    pass
d=int(sys.argv[1]); ORDER=int(sys.argv[2]) if len(sys.argv)>2 else 4; UV=sys.argv[3] if len(sys.argv)>3 else 'i'
basis=list(parts(d)); nb=len(basis)
rows=[]
for _ in range(2*nb+10):
    A,B=random.randint(-20,20),random.randint(-20,20)
    u=[random.randint(-9,9) for _ in range(3)]; u.append(-sum(u))
    w=[random.randint(-9,9) for _ in range(3)]; w.append(-sum(w))
    E=ev(basis,psums([A]*4+[B]*4+[-4*(A+B)],u+w+[0]))
    for o in range(ORDER): rows.append([E[j][o] for j in range(nb)])
ns=sp.Matrix(rows).nullspace()
E=ev(basis,psums([a]*4+[b]*4+[-4*(a+b)],([1,sp.I,-1,-sp.I] if UV=='i' else [1,-1,1,-1])+[0]*5,True),True)
forms=[sp.expand(sum(v[j]*E[j][ORDER] for j in range(nb))) for v in ns]
forms=[f for f in forms if f!=0]
g=forms[0]
for f in forms[1:]: g=sp.gcd(g,f)
print(f"d={d} order>={ORDER} dim={len(ns)} nonzero forms={len(forms)} gcd at u:", sp.factor(g))
