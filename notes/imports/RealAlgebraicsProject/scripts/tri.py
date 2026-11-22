import numpy as np, glob
from hilb import *
exec(open('ca_class.py').read().split('for f in')[0])
def linestruct(E,al):
    B=np.linalg.svd(al.reshape(1,3))[2][1:]; L=np.stack([E@B[0],E@B[1]],1)
    L/=np.linalg.norm(L)
    zeros=[i for i in range(9) if np.linalg.norm(L[i])<1e-6]
    pairs=[(i,j) for i in range(9) for j in range(i+1,9) if np.linalg.norm(L[i]+L[j])<1e-6 and i not in zeros]
    eq=[(i,j) for i in range(9) for j in range(i+1,9) if np.linalg.norm(L[i]-L[j])<1e-6 and i not in zeros]
    return 'zeros%s pairs%s equal%s'%(zeros,pairs,eq)
for f in sorted(glob.glob('ca_*.npy')):
    u=np.load(f); E=u[:27].reshape(9,3); A=qmat(u[27:33]); l=u[33:36]
    w,V=np.linalg.eigh(A); i=[k for k in range(3) if abs(w[k])>1e-5*max(abs(w))]
    if len(i)!=2: continue
    a,b=V[:,i[0]]*np.sqrt(abs(w[i[0]])),V[:,i[1]]*np.sqrt(abs(w[i[1]]))
    print(f); 
    for nm,al in (('m1',a+b),('m2',a-b),("m'",l)): print('   ',nm,linestruct(E,al))
