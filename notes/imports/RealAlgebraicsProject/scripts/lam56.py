# degree of the map Sigma -> P^4 of 3-spaces through the plane <l1,l3>, composed with a generic projection to P^1:
# number of points of Sigma (a != 0, s != 0, Q' != Q) on a generic hyperplane H containing Q, v1, v3
import sys, random
from sigma56 import *
seed=int(sys.argv[1]); rng,Q,v1,v3,lam,m=mk(seed)
def solve_h():
    # random h with h.Q = h.v1 = h.v3 = 0 (and h not multiple of the trace) : pick random 6 coords, solve 3 linear eqs
    import itertools
    while True:
        h=[rng.randrange(p) for _ in range(9)]
        # adjust last 3 coords
        M=[[Q[6],Q[7],Q[8]],[v1[6],v1[7],v1[8]],[v3[6],v3[7],v3[8]]]
        b=[(-sum(h[i]*X[i] for i in range(6)))%p for X in (Q,v1,v3)]
        # solve 3x3 mod p
        A=[M[i]+[b[i]] for i in range(3)]
        ok=True
        for c in range(3):
            piv=next((r for r in range(c,3) if A[r][c]%p),None)
            if piv is None: ok=False;break
            A[c],A[piv]=A[piv],A[c]; iv=pow(A[c][c],p-2,p); A[c]=[x*iv%p for x in A[c]]
            for r in range(3):
                if r!=c and A[r][c]: f=A[r][c]; A[r]=[(A[r][j]-f*A[c][j])%p for j in range(4)]
        if ok:
            h[6],h[7],h[8]=A[0][3],A[1][3],A[2][3]; return h
eqs=system(Q,v1,v3,lam,m,a="a")
for k in range(2):
    h=solve_h()
    assert sum(h[i]*Q[i] for i in range(9))%p==0
    sc=f"ring r={p},({VARS},a),dp; ideal I={','.join(eqs)},{'+'.join(f'({h[i]})*y{i+1}' for i in range(9))}; ideal G=std(I); print(vdim(G));"
    print('Lambda-map degree', run(sc).split())
