"""C_a: conics in L_135 whose residual line (l3 = 0 in the plane) also lies in L_135.
Extra equations: p5 restricted to the residual line = 0 (6).  Then check the tangent space of the
plain conic system F at each C_a member (kernel 12 = smooth point of C; 13+ = meets another sheet)."""
import numpy as np, sys
from hilb import *
seed=int(sys.argv[1]); starts=int(sys.argv[2]); rng=np.random.default_rng(seed)
def p5line(u):
    E=u[:27].reshape(9,3); l=u[33:36]
    # residual line: points with l.(x,y,z)=0; basis via cross products with fixed vectors (smooth in l)
    b0=np.cross(l,[0.3,0.7,0.2]); b1=np.cross(l,b0)
    m0,m1=E@b0,E@b1
    return restrict(np.stack([m0,m1,0*m0],1),5)[[IDX[5][(5-j,j,0)] for j in range(6)]]
def G(u):
    E=u[:27].reshape(9,3)
    return np.concatenate([F(u),p5line(u),(E.T@E-np.eye(3))[np.triu_indices(3)],[u[27:33]@u[27:33]-1, u[33:36]@u[33:36]-1]])
def jacG(u,h=1e-6): return np.array([(G(u+h*e)-G(u-h*e))/(2*h) for e in np.eye(46)]).T
def lm(u):
    lam=1e-2; g=G(u); f=g@g
    for it in range(400):
        J=jacG(u); st=np.linalg.solve(J.T@J+lam*np.eye(46),J.T@g); un=u-st; gn=G(un); fn=gn@gn
        if fn<f: u,g,f=un,gn,fn; lam=max(lam/3,1e-12)
        else: lam*=4
        if f<1e-26 or lam>1e9: break
    return u,np.sqrt(f)
def qdet(u):
    q=u[27:33]; A=np.zeros((3,3))
    for k,ex in enumerate(M[2]):
        idx=[i for i in range(3) for _ in range(ex[i])]
        if idx[0]==idx[1]: A[idx[0],idx[0]]+=q[k]
        else: A[idx[0],idx[1]]+=q[k]/2; A[idx[1],idx[0]]+=q[k]/2
    return abs(np.linalg.det(A))/np.linalg.norm(A)**3
def degen(u):
    E=u[:27].reshape(9,3)
    if min(np.linalg.norm(E,axis=1))<1e-5: return 'zero'
    if min(np.linalg.norm(E[i]+E[j]) for i in range(9) for j in range(i+1,9))<1e-5: return 'pair'
    if min(np.linalg.norm(E[i]-E[j]) for i in range(9) for j in range(i+1,9))<1e-5: return 'equal'
    return None
res=[]
for s in range(starts):
    u,r=lm(rng.normal(size=46))
    if r>1e-11: res.append(('fail',)); continue
    d=degen(u)
    if d: res.append((d,)); continue
    sv=np.linalg.svd(jac(u),compute_uv=False)
    res.append(('ok',46-np.sum(sv>1e-6*sv[0]),sv[33]/sv[0],qdet(u)))
    np.save('ca_%d_%d.npy'%(seed,s),u)
from collections import Counter
print(Counter(r[0] for r in res))
for r in res:
    if r[0]=='ok': print('kernel %d  s34/s1 %.2e  conic det %.2e'%r[1:])
