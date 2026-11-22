# export the reduced M2 system (m2red.py) to msolve and run it
import sys, random, re, subprocess, time
from sing import run
seed=int(sys.argv[1]); p=int(sys.argv[2]) if len(sys.argv)>2 else 32003
rng=random.Random(seed); tau=rng.sample(range(1,p),9)
chi="*".join(f"(t-({x}))" for x in tau)
sc=f"""ring S={p},(t,z0,z1,z2,z3,q0,q1,q2,q3,e,u),dp;
poly R=q0+q1*t+q2*t^2+q3*t^3; poly Z=z0+z1*t+z2*t^2+z3*t^3;
poly F=Z^2-R*(1-R)*(1+e-e*R)^2; poly chi={chi};
poly nf=reduce(F,std(ideal(chi))); matrix C=coeffs(nf,t);
ideal I; int i; for(i=1;i<=nrows(C);i++){{I=I+C[i,1];}} I=I,u*q1-1;
write(":w m2_{seed}.polys", I);"""
run(sc)
polys=[x.strip() for x in open(f"m2_{seed}.polys").read().replace("\n","").split(",")]
open(f"m2_{seed}.ms","w").write("z0,z1,z2,z3,q0,q1,q2,q3,e,u\n"+str(p)+"\n"+",\n".join(polys)+"\n")
print(len(polys),"polys; degrees", sorted(set(len(re.findall(r'[zqeu]\d?',x)) for x in polys))[:3])
t0=time.time()
r=subprocess.run(["msolve","-v","1","-f",f"m2_{seed}.ms","-o",f"m2_{seed}.out"],capture_output=True,text=True,timeout=int(sys.argv[3]) if len(sys.argv)>3 else 100000)
print(r.stdout[-1500:]); print("time",time.time()-t0)
