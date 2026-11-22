# Session 6: fixed loci of abelian p-subgroups on Q4, D (Theorem J). Needs absub.txt from absub.g.
# Fixed loci of abelian p-subgroups H of PSL(2,8), A9, S9 on P(V), V = trace-zero C^9,
# and whether they meet Q4 = 6p4 - p2^2, D = Q4 ∩ Q5 (Q5 = 18p5 - 5p2p3), T = {p2=...=p7=0}.
import numpy as np, itertools, ast
def P(x,k): return np.sum(x**k)
def Q4(x): return 6*P(x,4)-P(x,2)**2
def Q5(x): return 18*P(x,5)-5*P(x,2)*P(x,3)
def nrm(x): return x/np.linalg.norm(x)
def eigenspaces(ords, els):
    # characters indexed by k in prod Z/o_i : chi_k(h_e) = prod exp(2 pi i k_i e_i / o_i)
    perms=[np.array(p)-1 for p,_ in els]; exps=[e for _,e in els]
    out=[]
    for k in itertools.product(*[range(o) for o in ords]):
        chi=[np.exp(2j*np.pi*sum(ki*ei/oi for ki,ei,oi in zip(k,e,ords))) for e in exps]
        # projector onto chi-isotypic part of C^9: P = 1/|H| sum conj(chi(h)) h ; h acts by (h x)_{h(j)} = x_j
        M=np.zeros((9,9),complex)
        for p,c in zip(perms,chi):
            A=np.zeros((9,9)); A[p,np.arange(9)]=1
            M+=np.conj(c)*A
        M/=len(perms)
        # restrict to trace zero
        Pr=np.eye(9)-np.ones((9,9))/9
        M=Pr@M@Pr
        u,s,vh=np.linalg.svd(M); r=int(np.sum(s>1e-9))
        if r: out.append((k,u[:,:r]))
    return out
def meets_line(B, eqs):
    # B: 9x2 basis. Points x = B@(1,mu) or B@(0,1). Use roots of first eq.
    a,b=B[:,0],B[:,1]
    f=eqs[0]; deg=4
    mus=np.linspace(-2,2,deg+1)+0.3j
    vals=[f(a+m*b) for m in mus]
    c=np.polyfit(mus,vals,deg)
    cands=[a+m*b for m in np.roots(c)]+[b]
    best=min(max(abs(g(nrm(x))) for g in eqs) for x in cands)
    return best
res={}
for line in open('absub.txt'):
    G,p,ords,els=line.strip().split('|'); ords=ast.literal_eval(ords); els=ast.literal_eval(els)
    rep=[]
    for k,B in eigenspaces(ords,els):
        d=B.shape[1]
        if d>=3: q4=True; dd=True
        elif d==2:
            q4=True
            dd = meets_line(B,[Q4,Q5])<1e-8
        else:
            x=nrm(B[:,0]); q4=abs(Q4(x))<1e-9; dd=q4 and abs(Q5(x))<1e-9
        rep.append((d,q4,dd))
    anyQ4=any(r[1] for r in rep); anyD=any(r[2] for r in rep)
    print(f"{G:6s} p={p} H={ords!s:14s} eigenspace dims={sorted(r[0] for r in rep)}  fixed pt on Q4: {anyQ4}  on D: {anyD}")
