#!/usr/bin/env python3
"""Row G (Bezier x P-quartic graph) degree check, mod p, with Singular.

Usage:
  python3 G_check.py line <seed> [p]        # random F_p line tau = tau0 + s*tau1: prints dim, vdim, deg of eliminant,
                                            #   squarefree test (-1 = squarefree), factor degrees
  python3 G_check.py irr <seed>             # one small integer line, factored mod 16 primes; prints the common
                                            #   subset sums of the factor degrees ({0, 180} = no split over Q)
Needs Singular: apt-get update && apt-get install -y singular  (about a minute).
Condition (artifact of Nov 19, repo commit 2536d12): X = t^3 + a t^2 + b t; the 5x3 matrix of the t^4..t^8
coefficients of X^k mod chi_tau (k = 2, 3, 4) has rank <= 2.
Nov 19 runs: line 7, line 8 (180, squarefree; factor degrees 23+76+81 and 1+1+2+4+11+30+31+100);
irr 11 (16 primes, common subset sums {0, 180}). Each Singular run takes well under a second.
"""
import random, subprocess, sys

PRIMES = [32003, 32009, 32027, 32029, 32051, 32057, 32059, 32063, 32069, 32077,
          32083, 32089, 32099, 32117, 32119, 32141]

def script(p, t0, t1):
    chi = "*".join(f"(t-({a})-({b})*s)" for a, b in zip(t0, t1))
    return f"""
ring r=({p}),(t,a,b,s),dp; poly chi = {chi}; poly X = t^3+a*t^2+b*t;
ideal G = chi; matrix M[5][3]; matrix C; int k,j; poly R;
for(k=2;k<=4;k++){{ R=reduce(X^k,G); C=coeffs(R+t^9,t); for(j=4;j<=8;j++){{ M[j-3,k-1]=C[j+1,1]; }} }}
ring r2=({p}),(a,b,s),dp; matrix M=imap(r,M); ideal J=std(minor(M,3));
print("dim "+string(dim(J))+" vdim "+string(vdim(J)));
poly f=eliminate(J,a*b)[1]; ideal sq=f,diff(f,s);
print("deg "+string(deg(f))+" sqf "+string(dim(std(sq))));
list L=factorize(f); string o=""; for(k=1;k<=size(L[1]);k++){{ if(deg(L[1][k])>0){{ for(j=1;j<=L[2][k];j++){{o=o+string(deg(L[1][k]))+",";}} }} }} print("factors "+o);
quit;"""

def run(p, t0, t1):
    out = subprocess.run(["Singular", "-q"], input=script(p, t0, t1), capture_output=True, text=True, timeout=300).stdout
    d = {}
    for line in out.splitlines():
        w = line.split()
        if w and w[0] == "dim": d["dim"], d["vdim"] = int(w[1]), int(w[3])
        if w and w[0] == "deg": d["deg"], d["sqf"] = int(w[1]), int(w[3])
        if w and w[0] == "factors": d["factors"] = [int(x) for x in w[1].strip(",").split(",") if x]
    return d

def main():
    mode, seed = sys.argv[1], int(sys.argv[2])
    random.seed(seed)
    if mode == "line":
        p = int(sys.argv[3]) if len(sys.argv) > 3 else 32003
        t0 = [random.randrange(p) for _ in range(9)]; t1 = [random.randrange(p) for _ in range(9)]
        print(run(p, t0, t1))
    else:
        t0 = [random.randint(-20, 20) for _ in range(9)]; t1 = [random.randint(-20, 20) for _ in range(9)]
        common = None
        for p in PRIMES:
            d = run(p, t0, t1)
            print(p, d)
            if d.get("deg") != 180 or d.get("sqf") != -1:
                continue
            s = {0}
            for x in d["factors"]:
                s |= {y + x for y in s}
            common = s if common is None else common & s
        print("common subset sums:", sorted(common))

if __name__ == "__main__":
    main()
