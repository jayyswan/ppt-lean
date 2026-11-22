"""Session 34: check T_i = prod_{j!=i} det(L_i,L_j) = Phi(L_i) on ordinary lines,
and the rank of the binary quadratic Phi. Reads lines_good.npy, lines_lab.npy."""
import numpy as np
L=np.load('lines_good.npy'); lab=np.load('lines_lab.npy'); n=9
for C,k in zip(L,lab):
    C=C/np.linalg.norm(C,axis=1).mean()
    T=np.array([np.prod([C[i,0]*C[j,1]-C[i,1]*C[j,0] for j in range(n) if j!=i]) for i in range(n)])
    A=np.array([[x*x,x*y,y*y] for x,y in C])
    sol,res,_,_=np.linalg.lstsq(A/np.abs(T)[:,None],T/np.abs(T),rcond=None)
    rel=np.max(np.abs(A@sol-T)/np.abs(T))
    a,b,c=sol; disc=(b*b-4*a*c)/(a*a+b*b+c*c)
    print(k, 'rel %.1e'%rel, 'disc(Phi)/|Phi|^2 %.2e'%disc)

# canonical point P_O on ordinary lines: z_i = ell(L_i), Phi = ell^2
print('--- P_O on ordinary lines: normalised Q4, p7, p2 ---')
for C,k in zip(L,lab):
    if k!='gen': continue
    C=C/np.linalg.norm(C,axis=1).mean()
    T=np.array([np.prod([C[i,0]*C[j,1]-C[i,1]*C[j,0] for j in range(n) if j!=i]) for i in range(n)])
    A=np.array([[x*x,x*y,y*y] for x,y in C])
    a,b,c=np.linalg.lstsq(A/np.abs(T)[:,None],T/np.abs(T),rcond=None)[0]
    l=np.array([1.0,b/(2*a)]) if abs(a)>abs(c) else np.array([b/(2*c),1.0])
    z=C@l; z/=np.linalg.norm(z)
    p=lambda m: np.sum(z**m)
    # other points of the line for comparison
    w=C@np.array([0.3,1.0]); w/=np.linalg.norm(w); q=lambda m: np.sum(w**m)
    print('Q4(P_O) %+.3e  p7(P_O) %+.3e | Q4(rand) %+.3e  sign(T)' % (6*p(4)-p(2)**2, p(7), 6*q(4)-q(2)**2), np.sign(T*a).astype(int))
