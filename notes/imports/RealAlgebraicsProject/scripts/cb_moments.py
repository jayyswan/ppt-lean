"""Full (not only harmonic) moments sum_i M(Q_i) for monomials M of degree 1..7,
on the two populations.  Session 30."""
import numpy as np, itertools
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
def mom(Q,d):
    mon=[e for e in itertools.product(range(d+1),repeat=3) if sum(e)==d]
    v=np.array([np.sum(np.prod(Q**np.array(e),axis=1)) for e in mon])
    a=np.array([np.sum(np.abs(np.prod(Q**np.array(e),axis=1))) for e in mon])
    return np.max(np.abs(v))/np.max(a)
for t in ['pencil','gen']:
    rows=[[mom(Q,d) for d in range(1,8)] for Q,l in zip(Qs,lab) if l==t]
    print(t, len(rows))
    for r in rows[:5]: print('  '+' '.join('%.0e'%x for x in r))
