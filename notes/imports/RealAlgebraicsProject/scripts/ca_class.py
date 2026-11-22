import numpy as np, glob
from hilb import *
def qmat(q):
    A=np.zeros((3,3))
    for k,ex in enumerate(M[2]):
        idx=[i for i in range(3) for _ in range(ex[i])]
        if idx[0]==idx[1]: A[idx[0],idx[0]]+=q[k]
        else: A[idx[0],idx[1]]+=q[k]/2; A[idx[1],idx[0]]+=q[k]/2
    return A
for f in sorted(glob.glob('ca_*.npy')):
    u=np.load(f); E=u[:27].reshape(9,3); A=qmat(u[27:33]); l=u[33:36]
    w,V=np.linalg.eigh(A); w=w/np.max(abs(w))
    kd,s=kernel_dim(u)
    info='eig %s'%np.array2string(w,precision=3)
    if np.sum(abs(w)>1e-5)==2:
        # line pair: q = (alpha.x)(beta.x); lines = kernels of alpha, beta
        i=[k for k in range(3) if abs(w[k])>1e-5]; a,b=V[:,i[0]]*np.sqrt(abs(w[i[0]])),V[:,i[1]]*np.sqrt(abs(w[i[1]]))
        sg=np.sign(w[i[0]]*w[i[1]])
        if sg<0: al,be=a+b,a-b; info+=' real pair; p5 on lines: %.1e %.1e  residual %.1e'%(p5_on_line(E,al),p5_on_line(E,be),p5_on_line(E,l))
        else: info+=' complex-conjugate pair (real point only)'
    elif np.sum(abs(w)>1e-5)==1: info+=' double line'
    print(f, 'kernel',kd, info)
