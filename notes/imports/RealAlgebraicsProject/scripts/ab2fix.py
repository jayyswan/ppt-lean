# Reads ab2.out produced by: gap -q ab2.g > ab2.out. Lists abelian 2-subgroups of S9, A9 with no fixed point on D (session 8).
import numpy as np, re, ast
txt=open('ab2.out').read().replace('\n',' ')
blocks=re.split(r'GROUP',txt)[1:]
def Q4(x): p=lambda k: np.sum(x**k); return 6*p(4)-p(2)**2
def Q5(x): p=lambda k: np.sum(x**k); return 18*p(5)-5*p(2)*p(3)
def coeffs(f,u,v,deg):
    ls=np.exp(2j*np.pi*np.arange(deg+1)/(deg+1)); vals=np.array([f(l*u+v) for l in ls]); return np.fft.fft(vals)/(deg+1)
Pm=np.eye(9)-1/9
def eigspaces(gens):
    spaces=[np.linalg.qr(Pm@np.eye(9))[0][:,:8]]  # basis of V (orthonormal)
    U,s,_=np.linalg.svd(Pm); spaces=[U[:,:8]]
    for g in gens:
        M=np.zeros((9,9))
        for i,gi in enumerate(g): M[gi-1,i]=1
        new=[]
        for S in spaces:
            A=np.linalg.lstsq(S,M@S,rcond=None)[0]
            w,Vv=np.linalg.eig(A)
            for lam in np.unique(np.round(w,8)):
                idx=np.abs(w-lam)<1e-6
                B=S@Vv[:,idx]; B=np.linalg.qr(B)[0]; new.append(B)
        spaces=new
    return spaces
def meetsD(B):
    d=B.shape[1]
    if d>=3: return True,'dim%d'%d
    if d==1:
        x=B[:,0]; return (abs(Q4(x))<1e-8 and abs(Q5(x))<1e-8),'pt'
    u,v=B[:,0],B[:,1]
    c4=coeffs(Q4,u,v,4); c5=coeffs(Q5,u,v,5)
    if np.abs(c4).max()<1e-9: return True,'line in Q4'
    r=np.roots(c4[::-1])
    vals=[abs(np.polyval(c5[::-1],t)) for t in r]
    # also root at infinity if leading coef 0
    ok=any(vv<1e-7*max(1,np.abs(c5).max()*max(1,abs(t))**5) for vv,t in zip(vals,r))
    if abs(c4[4])<1e-9 and abs(c5[5])<1e-9: ok=True
    return ok,'line'
for blk in blocks:
    head,*subs=blk.split('SUB')
    print('GROUP order',head.split()[0],'#abelian 2-subgroup classes',head.split()[1])
    for s in subs:
        gens=ast.literal_eval(s.strip())
        sp=eigspaces(gens)
        res=[meetsD(B) for B in sp]
        if not any(r[0] for r in res):
            orbits=None
            print('  NO fixed point on D:',gens,'eigdims',sorted(B.shape[1] for B in sp))
