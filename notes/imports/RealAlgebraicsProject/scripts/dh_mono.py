# Session 40: local monodromy of Engine O around Delta_h = 0. Fix a=-3, U, loop b around 2 (h=(x-1)^2(x+2)).
# usage: python3 dh_mono.py U rad
import sys, numpy as np
from scipy.optimize import linear_sum_assignment
exec(open('load.py').read())
U=sys.argv[1]; rad=float(sys.argv[2])
P(f'Gb=substvec(G,[a,U],[-3,{U}])')
C=[]
for k in range(9,-1,-1):
    pk=P(f'polcoef(Gb,{k},x)')
    C.append([float(P('polcoef')(pk,j,P('b'))) for j in range(12)])
C=np.array(C)
def roots(bb): return np.roots(C@np.array([bb**j for j in range(12)]))
# other branch points in b near 2: roots of A, B in b
for nm in ('Au','Bu'):
    rr=P(f'polroots(substvec({nm},[a,U],[-3,{U}]))')
    print(nm,'b-roots near 2:',[complex(float(P('real')(z)),float(P('imag')(z))) for z in rr if abs(complex(float(P('real')(z)),float(P('imag')(z)))-2)<0.5])
b0=2+rad
r0=roots(b0); r=r0.copy()
for t in np.linspace(0,1,20001)[1:]:
    nr=roots(2+rad*np.exp(2j*np.pi*t)); D=np.abs(r[:,None]-nr[None,:]); i,j=linear_sum_assignment(D); r=nr[j[np.argsort(i)]]
p=[int(np.argmin(np.abs(r0-z))) for z in r]
seen=set();cyc=[]
for i in range(9):
    if i in seen: continue
    j=i;L=0
    while j not in seen: seen.add(j);j=p[j];L+=1
    cyc.append(L)
print('roots at start',np.round(r0,4))
print('cycle type',sorted(cyc,reverse=True),p)
