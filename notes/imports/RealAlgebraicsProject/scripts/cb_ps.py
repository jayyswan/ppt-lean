"""Which further power sums / invariants vanish identically on the conics,
by population.  Session 30."""
import numpy as np
from numpy.polynomial import polynomial as Pl
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
def ps(Q,m):
    tot=np.zeros(2*m+1); ab=np.zeros(2*m+1)
    for c in Q:
        p=Pl.polypow(c,m); tot[:len(p)]+=p; ab[:len(p)]+=np.abs(Pl.polypow(np.abs(c),m))
    return np.max(np.abs(tot))/np.max(ab)
def q4(Q):
    p2=sum(Pl.polypow(c,2) for c in Q); p4=sum(Pl.polypow(c,4) for c in Q)
    v=6*p4-Pl.polymul(p2,p2); return np.max(np.abs(v))/np.max(np.abs(6*p4))
for t in ['pencil','gen']:
    print(t)
    for Q in [Q for Q,l in zip(Qs,lab) if l==t][:5]:
        print('  '+' '.join('p%d:%.0e'%(m,ps(Q,m)) for m in [1,2,3,4,5,6,7,9,11])+'  Q4:%.0e'%q4(Q))
