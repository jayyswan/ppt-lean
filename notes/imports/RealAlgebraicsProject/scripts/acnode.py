# Session 36: acnode real form of the m=6 bubble.  Two-component side with an acnode: h ~ (v^2-1), points on the egg |v|<1,
# t = i v  =>  same t-problem F'(t)^2 = K (t^2+1)^5 with K < 0 and all u = t^2 in (-1, 0).
import numpy as np, sys
exec(open('cbubble.py').read().split("\nif __name__ == '__main__'")[0])
rng=np.random.default_rng(11)
Ks=-np.exp(np.linspace(np.log(1e-4),np.log(3e3),int(sys.argv[1]) if len(sys.argv)>1 else 60))
for K in Ks:
    sols=all_solutions(6,K,300,rng,rounds=2)
    for s in sols:
        u=s*s; uu=np.sort_complex(np.unique(np.round(u,8)))
        acn = np.all(np.abs(u.imag)<1e-8) and np.all((u.real>-1)&(u.real<0))
        print(f"K={K:.4g} nsol={len(sols)} u={np.array2string(uu,precision=4,max_line_width=200)} acnode-real={acn}",flush=True)
