import numpy as np, sys
sys.argv=['x','0','2','0']
exec(open('conics135.py').read().split('found = []')[0])
exec(open('conic_resid.py').read().split('out=[]')[0].split('Cs=np.load')[0])
Cs=np.load('curves_deg2.npy')
def resline(C):
    pt=lambda x,y,z: C[:,0]*x+C[:,1]*y+C[:,2]*z
    pts=np.random.default_rng(1).normal(size=(30,3))
    A=np.array([[ (y*y-x*z)*x,(y*y-x*z)*y,(y*y-x*z)*z] for x,y,z in pts])
    b=np.array([np.sum(pt(*q)**3) for q in pts]); l=np.linalg.lstsq(A,b,rcond=None)[0]
    vt=np.linalg.svd(l.reshape(1,3))[2]; m0,m1=pt(*vt[1]),pt(*vt[2])
    M=np.vstack([m0,m1]); # projector onto span as plucker-invariant
    Q,_=np.linalg.qr(M.T); return Q@Q.T
def p5res(C):
    pt=lambda x,y,z: C[:,0]*x+C[:,1]*y+C[:,2]*z
    pts=np.random.default_rng(1).normal(size=(30,3))
    A=np.array([[ (y*y-x*z)*x,(y*y-x*z)*y,(y*y-x*z)*z] for x,y,z in pts])
    b=np.array([np.sum(pt(*q)**3) for q in pts]); l=np.linalg.lstsq(A,b,rcond=None)[0]
    vt=np.linalg.svd(l.reshape(1,3))[2]; m0,m1=pt(*vt[1]),pt(*vt[2])
    ts=np.linspace(-1,1,6); return np.max(np.abs(np.polyfit(ts,[np.sum((m0+t*m1)**5) for t in ts],5)))
rng=np.random.default_rng(3)
for C in Cs:
    if np.linalg.svd(C,compute_uv=False)[-1]<0.02 or any(np.linalg.norm(C[i]+C[j])<1e-6 for i in range(n) for j in range(i+1,n)): continue
    if p5res(C)>1e-10: continue
    F,J=eqs(C); N=np.linalg.svd(J)[2][21:]  # tangent incl gauge (6 dims)
    P0=resline(C); diffs=[]
    for k in range(12):
        D=C+1e-4*(rng.normal(size=6)@N).reshape(n,3)
        D,r=solve(D)
        diffs.append((resline(D)-P0).ravel()); 
    sv=np.linalg.svd(np.array(diffs),compute_uv=False)
    print('type-a conic: rank of residual-line motion', np.round(sv[:4]/sv[0],5), ' still type a?', p5res(D)<1e-9)
