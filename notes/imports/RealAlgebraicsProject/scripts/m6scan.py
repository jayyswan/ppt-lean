# Session 35: fine K-scan of the m=6 bubble (P = t^2+1 normalisation).
# For each K: number of distinct complex solutions, and the class of u = t^2:
#   'one'  = all u real > 0 (real one-component core), 'two' = all u real < -1 (real two-component core, needs K>0),
#   'mix'  = otherwise.  usage: python3 m6scan.py <nK> <starts> [seed]
import sys, numpy as np
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
nK=int(sys.argv[1]); st=int(sys.argv[2]); rng=np.random.default_rng(int(sys.argv[3]) if len(sys.argv)>3 else 0)
Ks=np.concatenate([np.logspace(-4,5,nK)])
counts={}
for K in Ks:
    sols=all_solutions(6,K,st,rng,rounds=2)
    cls=[]
    for s in sols:
        u=s*s
        if np.abs(u.imag).max()<1e-7 and (u.real>0).all(): cls.append('one')
        elif np.abs(u.imag).max()<1e-7 and (u.real<-1).all(): cls.append('two')
        else: cls.append('mix')
    key=(len(sols),tuple(sorted(cls)))
    counts.setdefault(key,[]).append(K)
for k,v in counts.items(): print(k, "K in [%.4g, %.4g], %d values"%(min(v),max(v),len(v)))
