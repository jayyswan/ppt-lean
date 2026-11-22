# Session 14: exact degree-14 invariant R14, order 4 along Pi, whose normal quartic
# c1 (sum u^2)^2 + c2 sum u^4 has ord_{a=b} c2 = 4 <= ord_{a=b} c1 near x8.
import pickle, random, sympy as sp, sys
import ord4
from math import comb
from ord4 import parts
random.seed(5)
P = sp.symbols('p2:10')
# exact space of degree-14 invariants of order >= 4 along Pi (as in radicands13.space)
exec(open('radicands13.py').read().split("h6=-69")[0].split("P=sp.symbols('p2:10')")[1].replace('def mono','def mono'), globals())
S14 = space(14, 4)
print('dim', len(S14))
# exact evaluation: big prime modulus, then lift
q = sp.nextprime(10**120)
while q % 4 != 1: q = sp.nextprime(q)
q = int(q)
import evenx8
ord4.p = q; evenx8.p = q
Iq = pow(sp.primitive_root(q) if False else 3, (q-1)//4, q)
while Iq*Iq % q != q-1:
    g = random.randrange(2, q); Iq = pow(g, (q-1)//4, q)
evenx8.I = Iq
def lift(x): x %= q; return x - q if x > q//2 else x
ui = [1, Iq, q-1, q-Iq] + [0]*5
um = [1, q-1, 1, q-1] + [0]*5
Pu = evenx8.psums2(ui); Pm = evenx8.psums2(um)
def series(f, PS):
    poly = sp.Poly(f, *P)
    tot = [0]*evenx8.T
    for mon, c in poly.terms():
        lam = [k+2 for k, e in enumerate(mon) for _ in range(e)]
        S = evenx8.ev(lam, PS)
        for i in range(evenx8.T): tot[i] = (tot[i] + int(c)*S[i][4]) % q
    return [lift(x) for x in tot]
rows = []
C2 = []; C1 = []
for f in S14:
    C2.append(series(f, Pu)); C1.append(series(f, Pm))
print('Q(u_i)(t):', C2); print('Q(u_-1)(t):', C1)
M = sp.Matrix([[C2[j][i] for j in range(len(S14))] for i in range(4)] + [[C1[j][i] for j in range(len(S14))] for i in range(4)])
ns = M.nullspace()
print('solutions', len(ns))
pickle.dump(dict(S14=[str(f) for f in S14], C2=C2, C1=C1, ns=[[str(x) for x in v] for v in ns]), open('r14.pkl','wb'))
