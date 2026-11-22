# Row M2 (Bezier x egg), session 57, reduced form.
# Egg (normalised a = 1/2): x = th^2/(1+th^2), D = d0 + d1 x, y = D (th-1)^2 / (2(1+th^2)).
# With r = 1/(1+th^2) = R(tau) (R cubic: the Bezier x-coordinate, after the affine placement) and
# s = th*r (s^2 = r(1-r)), the y-condition y in W4 = span(1,tau,tau^2,tau^3) is  s*(1+e-e*r) = Z(tau), Z cubic, e = d1/d0.
# So:  chi_tau | F := Z^2 - R(1-R)(1+e-eR)^2   (deg 12), 9 equations in R (4), Z (4), e.
# Solutions (R, e, Z) and (R, e, -Z) are the egg points th and -th: theta-count N = #solutions, quotient N/2.
import sys, random
from sing import run
seed=int(sys.argv[1]); mode=sys.argv[2]; p=int(sys.argv[3]) if len(sys.argv)>3 else 32003
rng=random.Random(seed)
def script(tau, extra=""):
    chi="*".join(f"(t-({x}))" for x in tau)
    return f"""ring S={p},(t,w,z0,z1,z2,z3,q0,q1,q2,q3,e,u),dp; option(redSB);
poly R=q0+q1*t+q2*t^2+q3*t^3; poly Z=z0+z1*t+z2*t^2+z3*t^3;
poly F=Z^2-R*(1-R)*(1+e-e*R)^2; poly chi={chi};
poly nf=reduce(F,std(ideal(chi))); matrix C=coeffs(nf,t);
ideal I; int i; for(i=1;i<=nrows(C);i++){{I=I+C[i,1];}}
I=I,u*q1-1,t{extra};
"""
if mode=='count':
    for k in range(int(sys.argv[4]) if len(sys.argv)>4 else 1):
        tau=rng.sample(range(1,p),9)
        w="+".join(f"({rng.randrange(p)})*{v}" for v in ["z0","z1","z2","z3","q0","q1","q2","q3","e"])
        sc=script(tau)+f"""I=I,w-({w}); ideal G=std(I); print(vdim(G)); 
ideal E=eliminate(G,t*z0*z1*z2*z3*q0*q1*q2*q3*e*u); poly f=E[1]; print(deg(f));
list L=factorize(f); string st=""; for(i=1;i<=size(L[1]);i++){{st=st+string(deg(L[1][i]))+"^"+string(L[2][i])+" ";}} print(st);
// quotient by Z -> -Z : eliminate to a Z-even coordinate
"""
        print(run(sc,timeout=3000).split())
