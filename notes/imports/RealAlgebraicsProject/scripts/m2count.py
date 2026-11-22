# Row M2 (Bezier x egg), session 57: for a fixed generator tau (split model over F_p, tau_1..tau_9 in F_p),
# count egg parameters theta in K (x C^9) with x(theta)=theta^2/(1+theta^2) in W4=span(1,tau,tau^2,tau^3)
# and y(theta) = D(theta)(theta-1)^2/(2(1+theta^2)) in W4 for some shape d0:d1 (chart d0=1, e=d1/d0).
# Variables r_j = 1/(1+theta_j^2). W4-membership of z: sum_j tau_j^m z_j / chi'(tau_j) = 0, m=0..4.
import sys, random
from sing import run
p=int(sys.argv[3]) if len(sys.argv)>3 else 32003
seed=int(sys.argv[1]); mode=sys.argv[2]
rng=random.Random(seed)
def instance():
    tau=rng.sample(range(1,p),9)
    c=[]
    for m in range(5):
        row=[]
        for j in range(9):
            d=1
            for k in range(9):
                if k!=j: d=d*(tau[j]-tau[k])%p
            row.append(pow(tau[j],m,p)*pow(d,p-2,p)%p)
        c.append(row)
    th=[f"t{j+1}" for j in range(9)]; r=[f"r{j+1}" for j in range(9)]
    eqs=[f"{r[j]}*(1+{th[j]}^2)-1" for j in range(9)]
    eqs+=["+".join(f"({c[m][j]})*{r[j]}" for j in range(9)) for m in range(5)]
    # y_j = A_j + e B_j, A_j=(t-1)^2 r/2, B_j = t^2 (t-1)^2 r^2/2 ; drop the common 1/2
    eqs+=["+".join(f"({c[m][j]})*(({th[j]}-1)^2*{r[j]}+e*{th[j]}^2*({th[j]}-1)^2*{r[j]}^2)" for j in range(9)) for m in range(5)]
    eqs+=["u*(r1-r2)-1"]
    return tau,eqs
V="t1,t2,t3,t4,t5,t6,t7,t8,t9,r1,r2,r3,r4,r5,r6,r7,r8,r9,e,u"
if mode=='count':
    tau,eqs=instance()
    w="+".join(f"({rng.randrange(p)})*t{j+1}" for j in range(9))+f"+({rng.randrange(p)})*e"
    sc=(f"ring R={p},(w,{V}),dp; option(redSB); ideal I={','.join(eqs)},w-({w}); ideal G=std(I); print(vdim(G)); print(dim(G));"
        f"ideal E=eliminate(G,t1*t2*t3*t4*t5*t6*t7*t8*t9*r1*r2*r3*r4*r5*r6*r7*r8*r9*e*u); poly f=E[1]; print(deg(f));"
        f"list L=factorize(f); int i; string st=\"\"; for(i=1;i<=size(L[1]);i++){{st=st+string(deg(L[1][i]))+\"^\"+string(L[2][i])+\" \";}} print(st);")
    print(tau); print(run(sc,timeout=3000))
