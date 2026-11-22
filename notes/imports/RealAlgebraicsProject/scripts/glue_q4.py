# Session 35: Q4|line real roots on glued real S_ord lines near the nodal end. usage: python3 glue_q4.py <beta> <L list>
import sys, numpy as np, io, contextlib
beta=sys.argv[1]; Ls=sys.argv[2].split(',')
src=open('glue.py').read()
stats=[]
for L in Ls:
    sys.argv=['glue.py',beta,L,'1']
    g={}
    buf=io.StringIO()
    # run glue up to the outer solutions, then reuse its pieces
    pre=src.split("for xo in outs:")[0]
    with contextlib.redirect_stdout(buf): exec(pre,g)
    for xo in g['outs']:
        Lin=float(L)-np.sum(np.log(np.abs(xo))); K=np.exp(2*Lin)
        if not (0<K<3.45): stats.append((L,'nocore')); continue
        cs=g['all_solutions'](6,K,600,g['rng'],rounds=2); t=np.sort(cs[0].real); b=float(beta)
        h=lambda x:(x+1)*(x*x+b*b)
        x0=np.concatenate([b*t,xo]); Ff=lambda x:g['V'](x,h)-float(L)
        def Jf(x):
            d=x[:,None]-x[None,:]; np.fill_diagonal(d,1); iD=1/d; np.fill_diagonal(iD,0)
            J=-iD; np.fill_diagonal(J,iD.sum(1)-2.5*(1/(x+1)+2*x/(x*x+b*b))); return J
        x,r=g['newton_real'](x0,Ff,Jf,80)
        if r>1e-9: stats.append((L,'fail')); continue
        Fp=np.array([np.prod([x[i]-x[j] for j in range(9) if j!=i]) for i in range(9)])
        y=np.sign(Fp)*np.sqrt(h(x)); Z=1/y; A=x/y
        Z/=np.abs(Z).max(); A/=np.abs(A).max()
        # Q4(s) = 6 p4 - p2^2 on Z + s A
        P=lambda k: np.polynomial.polynomial.polypow
        def ps(k):
            c=np.zeros(k+1)
            for i in range(9): c+=np.polynomial.polynomial.polypow([Z[i],A[i]],k)
            return c
        q=6*ps(4)-np.polynomial.polynomial.polymul(ps(2),ps(2))
        rts=np.roots(q[::-1]); nreal=int(np.sum(np.abs(rts.imag)<1e-9*np.abs(rts).max()))
        stats.append((L,nreal,round(K,3),np.round(xo,3).tolist()))
for s in stats: print(s)
