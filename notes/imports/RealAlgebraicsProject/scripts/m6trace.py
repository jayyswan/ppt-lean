# Session 35: trace the unique m=6 bubble solution over K; print u_i = t_i^2 (3 values).
# one-component real config <=> all u_i > 0 real; two-component real config (t = i v) <=> all u_i < -1 real, K>0.
import numpy as np
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
rng=np.random.default_rng(7)
for K in [1e-6,1e-4,1e-2,0.1,0.5,1,2,3,4,5,6,8,10,20,35,36,37,50,100,1e3,1e4,1e6,-1e-4,-0.1,-1,-10,-36,-100,-1e4]:
    sols=all_solutions(6,K,800,rng,rounds=3)
    for s in sols:
        u=np.sort_complex(np.unique(np.round(s*s,9)))
        print(f"K={K:<9g} u =",np.array2string(u,precision=5,max_line_width=200))
