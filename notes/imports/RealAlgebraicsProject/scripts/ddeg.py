# Validation: degree of D = {nonics C^3 + A, deg A <= 3} (cone in P^8) by the same monodromy loop. Expect 20.
import numpy as np, sys
P=np.polynomial.polynomial
rng=np.random.default_rng(int(sys.argv[1]))
def crand(*sh): return rng.normal(size=sh)+1j*rng.normal(size=sh)
def pad(c,n=10):
    o=np.zeros(n,complex); o[:len(c)]=c; return o
def system(x,Z):
    z0,z1,z2=Z; u,w=x[:2]; C=np.append(x[2:5],1); A=x[5:9]
    z=z0+u*z1+w*z2; M=P.polyfromroots(z)
    E=pad(M)-pad(P.polypow(C,3))-pad(A)
    J=np.zeros((10,9),complex)
    for j in range(9):
        Mj=P.polyfromroots(np.delete(z,j)); J[:,0]-=pad(Mj)*z1[j]; J[:,1]-=pad(Mj)*z2[j]
    C2=P.polypow(C,2)
    for i in range(3):
        ti=np.zeros(i+1,complex); ti[i]=1; J[:,2+i]=-pad(3*P.polymul(C2,ti))
    for i in range(4): J[i,5+i]=-1
    return E[:9],J[:9]
exec(open('ydeg.py').read().split('def newton')[1].split('# start point')[0].join(['def newton','']))
C=np.append(crand(3),1); A=crand(4)
zs=P.polyroots(P.polyadd(P.polypow(C,3),A))
Z0=[zs,crand(9),crand(9)]
x0=np.concatenate([[0,0],C[:3],A]).astype(complex)
x0,ok=newton(x0,Z0); assert ok
key=lambda x:(round(x[0].real,6),round(x[0].imag,6),round(x[1].real,6),round(x[1].imag,6))
sols={key(x0):x0}; stable=0; loops=0
while stable<3:
    ZB=[crand(9),crand(9),crand(9)]; ZC=[crand(9),crand(9),crand(9)]; new=0
    for k,x in list(sols.items()):
        xa=track(x,Z0,ZB); xb=track(xa,ZB,ZC) if xa is not None else None
        xc=track(xb,ZC,Z0) if xb is not None else None
        if xc is not None and key(xc) not in sols: sols[key(xc)]=xc; new+=1
    loops+=1; print('loop',loops,len(sols),flush=True); stable=stable+1 if new==0 else 0
