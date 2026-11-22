import numpy as np, sys
sys.argv=['x','7']
exec(open('mono9.py').read().split('# start:')[0])
def M9(a,b): return np.array([[1,a[i],b[i],a[i]**2,a[i]*b[i],b[i]**2,a[i]**3,a[i]**2*b[i],a[i]*b[i]**2,b[i]**3] for i in range(9)])
R=np.random.default_rng(3).normal(size=(2,10))
def G(Y):
    y,v1,v2=Y[:12],Y[12:22],Y[22:32]; x=full(y); a,b=vec(x[:8]),vec(x[8:]); M=M9(a,b)
    return np.concatenate([eqs(x),M@v1,M@v2,[R[0]@v1-1,R[1]@v1,R[0]@v2,R[1]@v2-1]])
X=np.concatenate([np.load('dl_%d.npy'%s) for s in [1,2,3,4]])
for row in X[:6]:
    a,b=row[:9],row[9:]
    # gauge: transform so P1=(1,0),P2=(0,1) after relabel? lines saved already gauge-fixed? check
    g=np.linalg.inv(np.array([[a[1],b[1]],[a[2],b[2]]]).T)  # u-coords start at index1
    A=np.stack([a,b]); A2=g@A; a2,b2=A2[0],A2[1]
    y=np.concatenate([a2[3:9],b2[3:9]])
    M=M9(a2,b2); vh=np.linalg.svd(M)[2]; N=vh[-2:].T.conj()  # 10x2
    W=np.linalg.solve(R@N,np.eye(2)); V=N@W
    Y=np.concatenate([y,V[:,0],V[:,1]])
    for k in range(20):
        f=G(Y); Y=Y+np.linalg.lstsq(jac(G,Y),-f,rcond=None)[0]
    J=jac(G,Y); s=np.linalg.svd(J,compute_uv=False)
    print('resid %.1e'%np.linalg.norm(G(Y)), 'rank', int(np.sum(s>1e-6*s[0])), 'of 32; sv tail', ' '.join('%.1e'%v for v in s[-4:]))
