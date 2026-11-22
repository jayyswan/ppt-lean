"""Session 27: the 9 points Q_i=(Z_i,a_i) of a line; even polys {1,x^2,xy,y^2,x^4..y^4} vanishing on them."""
import numpy as np, sys
np.set_printoptions(precision=5, suppress=True, linewidth=170)
X=np.load(sys.argv[1]); x=X[0]
Z,a,b=x[:9],x[9:18],x[18:]
def M(Z,a): return np.stack([np.ones(9),Z*Z,Z*a,a*a,Z**4,Z**3*a,Z*Z*a*a,Z*a**3,a**4],1)  # rows: points
for nm,v in (('special',a),('ordinary',b)):
    A=M(Z,v); s=np.linalg.svd(A,compute_uv=False); print(nm,'sv',s)
    print('  rank [1,Z2,Za,a2]:',np.linalg.svd(A[:,:4],compute_uv=False))
    K=np.linalg.svd(A)[2][-(9-np.sum(s>1e-8*s[0])):]
    print('  vanishing even polys (coeffs 1,x2,xy,y2,x4,x3y,x2y2,xy3,y4):'); print(K)
print('--- ordinary: directions (y/x roots) of q2 and q4 for basis of pencil')
A=M(Z,b); K=np.linalg.svd(A)[2][-2:]
for k in K:
    q2=k[1:4]; q4=k[4:]
    # q2 = c1 x^2 + c2 xy + c3 y^2 ; roots in t=y/x of c3 t^2 + c2 t + c1
    print(np.roots(q2[::-1]), np.roots(q4[::-1]))
