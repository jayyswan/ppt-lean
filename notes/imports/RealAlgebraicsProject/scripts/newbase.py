import numpy as np, pickle, sys
from bl import *
Y0,c0,d=pickle.load(open('base.pkl','rb'))
rng=np.random.default_rng(int(sys.argv[1]))
d2=rng.normal(size=2)+1j*rng.normal(size=2); d2/=np.linalg.norm(d2)
dn=rng.normal(size=2)+1j*rng.normal(size=2); dn/=np.linalg.norm(dn)
c1=c0+0.8*d2
Y1=track(Y0,[c0,c0+0.4*d2+0.3j*dn,c1])
sv=np.linalg.svd(jacY(lambda v:H(v,c1),Y1),compute_uv=False)
print('min sv at new base %.2e'%sv[-1])
pickle.dump((Y1,c1,dn),open(sys.argv[2],'wb'))
