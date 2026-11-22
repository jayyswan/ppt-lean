"""Rank of harmonic evaluation: rows i, columns = coefficients of q_i(t)^m
(q_i normalised to unit vectors, so weights do not matter).  Generic 9 points:
rank min(9, 2m+1).  Also real roots of Q4 on the conic.  Session 30."""
import numpy as np
from numpy.polynomial import polynomial as Pl
from collections import Counter
Qs=np.load('cb_good.npy'); lab=np.load('cb_lab.npy')
def hr(Q,m):
    q=Q/np.linalg.norm(Q,axis=1)[:,None]
    M=np.array([Pl.polypow(c,m) for c in q]); M=M/np.linalg.norm(M,axis=0)
    s=np.linalg.svd(M,compute_uv=False); return int(np.sum(s>1e-9*s[0]))
def q4roots(Q):
    p2=sum(Pl.polypow(c,2) for c in Q); p4=sum(Pl.polypow(c,4) for c in Q)
    v=6*p4-Pl.polymul(p2,p2); r=np.roots(v[::-1]); return sum(abs(r.imag)<1e-7*max(1,abs(r).max()))
c=Counter()
for Q,l in zip(Qs,lab):
    c[(l,'harm ranks m=1..7',tuple(hr(Q,m) for m in range(1,8)))]+=1
    c[(l,'Q4 real roots',q4roots(Q)>0)]+=1
for k,v in sorted(c.items(),key=str): print(k,v)
