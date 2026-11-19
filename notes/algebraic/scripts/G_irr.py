import sys, random, subprocess, re
random.seed(11)
t0=[random.randint(-20,20) for _ in range(9)]; t1=[random.randint(-20,20) for _ in range(9)]
chi="*".join(f"(t-({t0[i]})-({t1[i]})*s)" for i in range(9))
primes=[32003,32009,32027,32029,32051,32057,32059,32063,32069,32077,32083,32089,32099,32117,32119,32141]
sums=None
for p in primes:
    src=f"""ring r=({p}),(t,a,b,s),dp; poly chi={chi}; poly X=t^3+a*t^2+b*t;
ideal G=std(ideal(chi)); matrix M[5][3]; matrix C; int k,j; poly R;
for(k=2;k<=4;k++){{ R=reduce(X^k,G); for(j=4;j<=8;j++){{ C=coeffs(R+t^9,t); M[j-3,k-1]=C[j+1,1]; }} }}
ring r2=({p}),(a,b,s),dp; matrix M=imap(r,M); ideal J=std(minor(M,3));
poly f=eliminate(J,a*b)[1]; list L=factorize(f); int i;
"DEG"; deg(f); deg(f/gcd(f,diff(f,s)));
for(i=1;i<=size(L[1]);i++){{ "F"; deg(L[1][i]); L[2][i]; }} quit;"""
    out=subprocess.run(["Singular","-q"],input=src,capture_output=True,text=True).stdout
    nums=[l.strip() for l in out.splitlines() if 'redefin' not in l]
    i=nums.index("DEG"); d,sq=int(nums[i+1]),int(nums[i+2])
    degs=[]
    j=i+3
    while j<len(nums):
        if nums[j]=="F": 
            dd,mm=int(nums[j+1]),int(nums[j+2])
            if dd>0: degs+= [dd]*mm
            j+=3
        else: j+=1
    if sq!=d: print(p,"not squarefree, skip",d,sq); continue
    ss={0}
    for x in degs: ss|={y+x for y in ss}
    sums=ss if sums is None else sums&ss
    print(p,d,sorted(degs),"common subset sums:",sorted(sums))
