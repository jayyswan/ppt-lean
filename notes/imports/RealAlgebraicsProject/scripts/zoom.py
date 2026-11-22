import numpy as np, pickle, sys
from bl import *
from circ import cycle_type
BASE=sys.argv[1]; Y0,c0,d=pickle.load(open(BASE,'rb'))
src=open('quad2.py').read(); exec(src[src.index('def pairs'):src.index('# reach the lower-left')])
x0,y0,side,m=float(sys.argv[2]),float(sys.argv[3]),float(sys.argv[4]),int(sys.argv[5]); h=side/m
ll0=x0+1j*y0
Yb=track(Y0,[c0,c0+(ll0+0.25j+0.1)*d,c0+(ll0-0.05*side-0.05j*side)*d]); sb=ll0-0.05*side-0.05j*side
for j in range(m):
    for i in range(m):
        ll=ll0+i*h+1j*j*h
        Y=track(Yb,[c0+sb*d,c0+(sb+ll)/2*d+0.0*d,c0+ll*d],h0=0.02)
        if Y is None: Y=track(Yb,[c0+sb*d,c0+(ll-0.3j*h)*d,c0+ll*d],h0=0.02)
        if Y is None: print(i,j,'reach fail',flush=True); continue
        out=loop(Y,[ll,ll+h,ll+h+1j*h,ll+1j*h,ll])
        if out is None: print(i,j,'loop fail',flush=True); continue
        sig,w=out; ct=cycle_type(sig)
        if ct!=[1]*9 or abs(w)>0.5: print(i,j,'cell %.3f%+.3fi'%(ll.real,ll.imag),'type',ct,'windD %.2f'%w,flush=True)
print('done',flush=True)
