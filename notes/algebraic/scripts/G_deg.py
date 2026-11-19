import sys, random
p=int(sys.argv[1]); seed=int(sys.argv[2])
random.seed(seed)
t0=[random.randrange(p) for _ in range(9)]; t1=[random.randrange(p) for _ in range(9)]
chi="*".join(f"(t-({t0[i]})-({t1[i]})*s)" for i in range(9))
coll="*".join(f"(({t1[i]}-{t1[j]})*s+{t0[i]}-{t0[j]})" for i in range(9) for j in range(i))
print(f"""
ring r=({p}),(t,a,b,s),dp;
poly chi={chi};
poly X=t^3+a*t^2+b*t;
ideal G=chi; G=std(G);
matrix M[5][3]; matrix C;
int k,j; poly R;
for(k=2;k<=4;k++){{ R=reduce(X^k,G);
  for(j=4;j<=8;j++){{ C=coeffs(R+t^9,t); M[j-3,k-1]=C[j+1,1]; }} }}
ring r2=({p}),(a,b,s),dp;
matrix M=imap(r,M);
ideal J=std(minor(M,3));
poly f=eliminate(J,a*b)[1];
poly cl={coll};
"p,seed,dim,vdim,deg_s,sqfree,gcd_with_collisions:";
{p}; {seed}; dim(J); vdim(J); deg(f); deg(f/gcd(f,diff(f,s))); deg(gcd(f,cl));
quit;
""")
