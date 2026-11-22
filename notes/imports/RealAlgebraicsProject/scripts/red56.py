# Reduced model of Sigma (S56): y = sum c_j b_j(a,s) in the kernel of the 5 linear conditions
# (Tr y, Tr x1 y, Tr x1^2 y, Tr x3 y, Tr x3^2 y), x1 = Q + a v1, x3 = Q + s v3; 4 remaining equations
# Tr y^2, Tr x1 y^2, Tr x3 y^2, Tr y^3 on (a, s, [c] in P^3).
# mode fib  <a0> : fibre degree over a = a0 (exact)
# mode wdeg      : degree of a generic linear form of y on Sigma
# mode ramw      : ramification count of a generic linear form (det of the 6x6 matrix [J ; dw])
import sys, random
from sing import run
from sigma56 import mk, p
seed=int(sys.argv[1]); mode=sys.argv[2]
rng,Q,v1,v3,lam,m=mk(seed)
cc=[rng.randrange(p) for _ in range(4)]; wy=[rng.randrange(p) for _ in range(9)]; mm=[rng.randrange(p) for _ in range(9)]
lQ=sum(lam[i]*Q[i] for i in range(9))%p; mQ=sum(mm[i]*Q[i] for i in range(9))%p
head=f"""ring r={p},(c1,c2,c3,c4,u1,u2,u3,u4,s,a),dp; option(redSB);
matrix Qv[1][9]={','.join(map(str,Q))}; matrix V1[1][9]={','.join(map(str,v1))}; matrix V3[1][9]={','.join(map(str,v3))};
matrix X1[1][9]; matrix X3[1][9]; int i,j;
for(i=1;i<=9;i++){{X1[1,i]=Qv[1,i]+a*V1[1,i]; X3[1,i]=Qv[1,i]+s*V3[1,i];}}
matrix M[5][9]; for(i=1;i<=9;i++){{M[1,i]=1; M[2,i]=X1[1,i]; M[3,i]=X1[1,i]^2; M[4,i]=X3[1,i]; M[5,i]=X3[1,i]^2;}}
// pivot columns 1..5, free columns 6..9 (Cramer)
matrix P[5][5]; for(i=1;i<=5;i++){{for(j=1;j<=5;j++){{P[i,j]=M[i,j];}}}}
poly D=det(P);
matrix B[4][9]; int f,k; matrix P2[5][5];
for(f=1;f<=4;f++){{ B[f,5+f]=D;
  for(k=1;k<=5;k++){{ P2=P; for(i=1;i<=5;i++){{P2[i,k]=M[i,5+f];}} B[f,k]=-det(P2); }} }}
matrix Y[1][9]; for(i=1;i<=9;i++){{Y[1,i]=c1*B[1,i]+c2*B[2,i]+c3*B[3,i]+c4*B[4,i];}}
poly e1,e2,e3,e4; for(i=1;i<=9;i++){{e1=e1+Y[1,i]^2; e2=e2+X1[1,i]*Y[1,i]^2; e3=e3+X3[1,i]*Y[1,i]^2; e4=e4+Y[1,i]^3;}}
poly ly,my,wy; for(i=1;i<=9;i++){{ly=ly+({'+'.join('0' for _ in range(1))})*Y[1,i];}}
matrix LA[1][9]={','.join(map(str,lam))}; matrix MM[1][9]={','.join(map(str,mm))}; matrix WY[1][9]={','.join(map(str,wy))};
for(i=1;i<=9;i++){{ly=ly+LA[1,i]*Y[1,i]; my=my+MM[1,i]*Y[1,i]; wy=wy+WY[1,i]*Y[1,i];}}
ideal F=e1,e2,e3,e4,{'+'.join(f'({cc[i]})*c{i+1}' for i in range(4))}-1;
ideal X=u1*s-1,u3*a-1,u4*D-1,u2*({mQ}*ly-({lQ})*my)-1;
"""
if mode=='fib':
    a0=int(sys.argv[3])
    sc=head+f"ideal G=std(F+X+ideal(a-({a0}))); print(vdim(G));"
elif mode=='wdeg':
    sc=head+f"ideal G=std(F+X+ideal(wy-({rng.randrange(p)})*ly)); print(vdim(G));"
elif mode=='ramw':
    # Sigma in chart: variables c1..c4,s,a ; map w = wy/ly ; critical: det [Jac(F) ; d(w)] with d(wy/ly) ~ ly*dwy - wy*dly
    sc=head+"""list vv=c1,c2,c3,c4,s,a; matrix JJ[6][6];
for(i=1;i<=5;i++){for(j=1;j<=6;j++){JJ[i,j]=diff(F[i],vv[j]);}}
for(j=1;j<=6;j++){JJ[6,j]=ly*diff(wy,vv[j])-wy*diff(ly,vv[j]);}
poly dd=det(JJ); print("detdeg "+string(deg(dd)));
ideal G=std(F+X+ideal(dd)); print("vdim "+string(vdim(G)));"""
elif mode=='rama':
    sc=head+"""list vv=c1,c2,c3,c4,s; matrix JJ[5][5];
for(i=1;i<=5;i++){for(j=1;j<=5;j++){JJ[i,j]=diff(F[i],vv[j]);}}
poly dd=det(JJ); print("detdeg "+string(deg(dd)));
ideal G=std(F+X+ideal(dd)); print("vdim "+string(vdim(G)));"""
import time; t=time.time(); print(run(sc,timeout=20000)); print("time",time.time()-t)
