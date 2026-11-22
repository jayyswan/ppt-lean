# Symbolic check: h7 vanishes to order >= 2 and m13 to order >= 4 along Pi (all normal directions);
# e4 to order >= 2 and n8 to order >= 4 at x54 (all directions).
import pickle, sympy as sp
from math import comb
R=pickle.load(open('radicands13.pkl','rb'))
P=sp.symbols('p2:10'); loc={f'p{k}':P[k-2] for k in range(2,10)}
F={k:sp.sympify(v,locals=loc) for k,v in R.items()}
a,b,t=sp.symbols('a b t')
def check(f,x,n,order):
    ser={k:[sp.expand(sum(comb(k,j)*xi**(k-j)*ni**j for xi,ni in zip(x,n))) if j<=k else 0 for j in range(order)] for k in range(2,10)}
    def smul(A,B): return [sp.expand(sum(A[i]*B[j-i] for i in range(j+1))) for j in range(order)]
    tot=[0]*order
    for term in sp.Add.make_args(f):
        c,mon=term.as_coeff_Mul(); s=[c]+[0]*(order-1)
        for fac in sp.Mul.make_args(mon):
            bs,e=fac.as_base_exp()
            for _ in range(int(e)): s=smul(s,ser[P.index(bs)+2])
        tot=[sp.expand(tot[j]+s[j]) for j in range(order)]
    return all(z==0 for z in tot)
u=sp.symbols('u1:4'); w=sp.symbols('w1:4')
nPi=list(u)+[-sum(u)]+list(w)+[-sum(w)]+[0]
Pi=[a]*4+[b]*4+[-4*(a+b)]
print("h7 order>=2 on Pi:",check(F['h7'],Pi,nPi,2))
print("m13 order>=4 on Pi:",check(F['m13'],Pi,nPi,4))
v=sp.symbols('v1:9'); nall=list(v)+[-sum(v)]
x54=[4]*4+[-5]*4+[4]
print("e4 order>=2 at x54:",check(F['e4'],x54,nall,2))
print("n8 order>=4 at x54:",check(F['n8'],x54,nall,4))
