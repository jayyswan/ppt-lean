import sys, numpy as np, itertools
exec(open('quad55.py').read().split("\ndef main")[0])
seed=int(sys.argv[1]); d=np.load(f'quad55_{seed}.npy')
rng,Q,v1,v3,x1=setup(seed)
sig=d[:,-1]; t=d[:,-2]
print('distinct sigma:', len({tuple(np.round([s.real,s.imag],5)) for s in sig}))
# residual conic
mons3=[m for m in itertools.combinations_with_replacement(range(4),3)]
def evalform(c, pts):  # not used
    pass
out=[]
for row in d:
    Qp,x3=row[:9],row[9:18]
    B=np.array([Q,x1,x3,Qp]).T  # 9x4
    rs=np.random.default_rng(0).standard_normal((40,4))+1j*np.random.default_rng(1).standard_normal((40,4))
    Y=rs@B.T
    p2=(Y**2).sum(1); p3=(Y**3).sum(1)
    # h13: plane through Q,x1,x3 -> coord d=0 ; h24: plane through x1,x3,Qp -> coord a=0
    h13=rs[:,3]; h24=rs[:,0]
    # p3 = h13*h24*hC + p2*m  -> unknowns hC(4), m(4)
    A=np.hstack([(h13*h24)[:,None]*rs, p2[:,None]*rs])
    sol,res,rk,sv=np.linalg.lstsq(A,p3,rcond=None)
    r=np.linalg.norm(A@sol-p3)/np.linalg.norm(p3)
    hC=sol[:4]
    # conic: points of S with hC=0 : param plane hC=0, solve p2=0
    # basis of plane
    N=np.linalg.svd(hC[None,:])[2][1:].conj()  # 3x4 rows orthonormal to hC? use null space
    Nb=np.linalg.svd(hC[None,:].astype(complex))[2][1:]
    Pb=(Nb@B.T)  # 3 points spanning plane in C^9
    G=Pb@Pb.T   # p2 bilinear Gram (no conj)
    ev=np.linalg.svd(G,compute_uv=False)
    # param conic: find point c0 on conic, then rational param
    out.append((r, ev[-1]/ev[0], np.linalg.svd(np.array([hC,[0,0,0,1],[1,0,0,0]]),compute_uv=False)[-1]))
out=np.array(out)
print('max lstsq resid', out[:,0].max().real, ' min conic nondeg', out[:,1].min().real, ' min indep(hC,h13,h24)', out[:,2].min().real)
