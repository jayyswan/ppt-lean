from tb_core import *
c,R=q3_roots()
print('roots',[mp.nstr(x,8) for x in R])
Qp=[(b,2*b**2+b**4) for b in R]
G=gammaQ_model(Qp)
print('sing vals', mp.nstr(G['S'][G['S'].rows-1],5))
print('residual',mp.nstr(G['check'],5))
W=G['W']; A,B=W.A,W.B
print('j(Gamma_Q)=',mp.nstr(jinv(A,B),25),' 4A^3+27B^2 sign',mp.sign(4*A**3+27*B**2),'B sign',mp.sign(B))
for P in G['pts']: print(' on E1:',mp.nstr(P[1]**2-(P[0]**3+A*P[0]+B),5))
