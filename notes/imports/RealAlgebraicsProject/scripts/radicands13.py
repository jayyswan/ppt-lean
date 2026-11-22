# Exact: h7 (order 2 along Pi), m12, m13 (order 4 along Pi, new modulo products), n8 and e4 at the (5,4) line.
# Checks the leading normal forms at the eigenvectors listed in the session 13 log section.
import random, sympy as sp
from math import comb
from ord4 import parts
random.seed(11)
P=sp.symbols('p2:10'); a,b,eps=sp.symbols('a b e')
def mono(lam): return sp.Mul(*[P[k-2] for k in lam])
def ser(x,n,R=5):
    return {k:[sum(comb(k,j)*xi**(k-j)*ni**j for xi,ni in zip(x,n)) if j<=k else 0 for j in range(R)] for k in range(2,10)}
def mul(A,B): return [sum(A[i]*B[j-i] for i in range(j+1)) for j in range(5)]
def space(d,order):
    basis=list(parts(d)); rows=[]
    for _ in range(3*len(basis)+10):
        A,B=random.randint(-20,20),random.randint(-20,20)
        u=[random.randint(-9,9) for _ in range(3)]; u.append(-sum(u))
        w=[random.randint(-9,9) for _ in range(3)]; w.append(-sum(w))
        S=ser([A]*4+[B]*4+[-4*(A+B)],u+w+[0])
        for lam in [None]: pass
        E=[]
        for lam in basis:
            s=[1,0,0,0,0]
            for k in lam: s=mul(s,S[k])
            E.append(s)
        for o in range(order): rows.append([E[j][o] for j in range(len(basis))])
    out=[]
    for v in sp.Matrix(rows).nullspace():
        v=v*sp.ilcm(*[sp.fraction(z)[1] for z in v]); g=sp.igcd(*[int(z) for z in v if z]); v=v/g
        out.append(sp.expand(sum(int(v[j])*mono(basis[j]) for j in range(len(basis)))))
    return out
h6=-69*P[0]**3+732*P[0]*P[2]+736*P[1]**2-1440*P[4]
h7=space(7,2)[0]
S13=space(13,4)
# m13: element of S13 with no p2^5 p3 ... pick the one independent of h6*h7 with the fewest terms
m13=min([f for f in S13 if sp.simplify(f/sp.expand(h6*h7)).is_number is False], key=lambda f: len(f.args))
S12=space(12,4)
m12=min([f for f in S12 if sp.simplify(f/sp.expand(h6**2)).is_number is False], key=lambda f: len(f.args))
n8=-1701*P[0]**2*P[2]+31752*P[0]*P[1]**2-107800*P[0]*P[4]-101920*P[1]*P[3]+94615*P[2]**2+220500*P[6]
e4=60*P[2]-7*P[0]**2
def val(f,x,n):
    sub={P[k-2]:sum((xi+eps*ni)**k for xi,ni in zip(x,n)) for k in range(2,10)}
    t=sp.Poly(sp.expand(f.subs(sub)),eps).terms()
    return min(t,key=lambda m:m[0][0])
I=sp.I
ui1=[1,I,-1,-I,0,0,0,0,0]; um1=[1,-1,1,-1,0,0,0,0,0]
Pi=[a]*4+[b]*4+[-4*(a+b)]
print("h7 =",h7); print("m12 =",m12); print("m13 =",m13)
for nm,f in [("h6",h6),("h7",h7)]:
    (k,),c=val(f,Pi,um1); print(nm,"at u_-1 (set1) over Pi: order",k,sp.factor(c))
for nm,f in [("m12",m12),("m13",m13)]:
    (k,),c=val(f,Pi,ui1); print(nm,"at u_i (set1) over Pi: order",k,sp.factor(c))
x54=[4]*4+[-5]*4+[4]
for nm,f,u in [("e4",e4,um1),("n8",n8,ui1)]:
    for which in (0,1):
        uu=u if which==0 else [0]*4+u[:4]+[0]
        (k,),c=val(f,x54,uu); print(nm,"at x54, set",which+1,": order",k,"coeff",c)
import pickle; pickle.dump({k:str(v) for k,v in dict(h7=h7,m12=m12,m13=m13,n8=n8,e4=e4).items()},open('radicands13.pkl','wb'))
