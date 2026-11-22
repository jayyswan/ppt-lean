# write the kernel system of ram56.py in msolve format
import sys, re
from sigma56 import *
from sing import run
seed=int(sys.argv[1]); which=sys.argv[2]
src=open('ram56.py').read()
# reuse ram56 construction by exec up to the run line
code=src.split("t=time.time()")[0]
sys.argv=['ram56.py',str(seed),which]
exec(code)
sc2=sc.replace('ideal G=std(I); print("vdim "+string(vdim(G)));','') + f'write(":w {which}_{seed}.polys", I);'
run(sc2)
txt=open(f"{which}_{seed}.polys").read()
txt=re.sub(r"k\((\d+)\)", r"k\1", txt)
nv=len(re.findall(r"k\((\d+)\)", sc.split("ideal I=")[0]))  # unused
vars_=[f"k{i+1}" for i in range(11 if which=='w' else 10)]+"u1,u2,u3,y1,y2,y3,y4,y5,y6,y7,y8,y9,s,a".split(",")
polys=[q.strip() for q in txt.replace("\n","").split(",")]
with open(f"ms_{which}_{seed}.in","w") as f:
    f.write(",".join(vars_)+"\n"+str(p)+"\n"+",\n".join(polys)+"\n")
print(len(polys), "polys")
