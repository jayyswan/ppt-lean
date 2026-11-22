# Ramification count of a map Sigma -> P^1 mod p, by a kernel vector of the Jacobian (S56).
# which = a : the map to l1 (coordinate a; fibre unknowns y1..y9, s)
#         s : the map to l3 (coordinate s; fibre unknowns y1..y9, a)
#         w : a generic linear form in y (tangent vector of the curve with dw = 0)
import sys, time
from sigma56 import *
seed=int(sys.argv[1]); which=sys.argv[2]
rng,Q,v1,v3,lam,m=mk(seed)
full=system(Q,v1,v3,lam,m,a="a")      # 10 core eqs + u1, u2, u3 exclusions
core=full[:10]; excl=full[10:]
allv=["y1","y2","y3","y4","y5","y6","y7","y8","y9","s","a"]
if which=='a': tv=allv[:10]; extra=[]
elif which=='s': tv=allv[:9]+["a"]; extra=[]
else:
    tv=allv; wc=[rng.randrange(p) for _ in range(9)]
    extra=["+".join(f"({wc[i]})*k({i+1})" for i in range(9))]
nv=len(tv)
nk=[rng.randrange(p) for _ in range(nv)]
sc=f"""ring r={p},(k(1..{nv}),u1,u2,u3,y1,y2,y3,y4,y5,y6,y7,y8,y9,s,a),dp; option(redSB);
ideal F={','.join(core)};
matrix J[10][{nv}]; int i,j;
list fv={','.join(tv)};
for(i=1;i<=10;i++){{for(j=1;j<={nv};j++){{J[i,j]=diff(F[i],fv[j]);}}}}
matrix kk[{nv}][1]; for(i=1;i<={nv};i++){{kk[i,1]=k(i);}}
matrix Jk=J*kk;
ideal I=F,ideal(Jk),{'+'.join(f'({nk[i]})*k({i+1})' for i in range(nv))}-1,{','.join(excl+extra)};
ideal G=std(I); print("vdim "+string(vdim(G)));
"""
t=time.time(); print(run(sc, timeout=20000)); print("time",time.time()-t)
