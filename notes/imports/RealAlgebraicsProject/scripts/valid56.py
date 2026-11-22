# validation of the kernel ramification count on C_Q (genus 13, degree 12): expect R = 2*13-2+2*12 = 48
import random
from sing import run
from setup56 import p, rand_V3
rng=random.Random(5); Q=rand_V3(rng)
v=[f"v{i+1}" for i in range(9)]
def T(*vecs): return "+".join("*".join(f"({x[i]})" for x in vecs) for i in range(9))
Qs=[str(x) for x in Q]; Q2=[str(x*x%p) for x in Q]
l=[[str(rng.randrange(p)) for _ in range(9)] for _ in range(3)]
core=[T(["1"]*9,v),T(Qs,v),T(Q2,v),T(v,v),T(Qs,v,v),T(v,v,v),T(l[0],v),T(l[1],v)+"-1"]
nk=[rng.randrange(p) for _ in range(9)]
sc=f"""ring r={p},(k(1..9),v1,v2,v3,v4,v5,v6,v7,v8,v9),dp; ideal F={','.join(core)};
matrix J[8][9]; int i,j; for(i=1;i<=8;i++){{for(j=1;j<=9;j++){{J[i,j]=diff(F[i],var(9+j));}}}}
matrix kk[9][1]; for(i=1;i<=9;i++){{kk[i,1]=k(i);}} matrix Jk=J*kk;
ideal I=F,ideal(Jk),{'+'.join(f'({l[2][i]})*k({i+1})' for i in range(9))},{'+'.join(f'({nk[i]})*k({i+1})' for i in range(9))}-1;
ideal G=std(I); print(vdim(G)); ideal H=std(F,{T(l[2],v)}-7); print(vdim(H));"""
print(run(sc).split())
