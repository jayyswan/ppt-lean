# e60.py -- session 60: exact counts mod p for row E with a fixed sextic S and P-valued dials (S59.4).
# Model: K split over F_p, tau in F_p^9.  Crossing: chi_{tau+s} * c(w) == S(a w^2 + b) mod deg <= 3,
# i.e. the 12 points {tau_i + s} u {z1,z2,z3} have power sums p_1..p_8 equal to those of the
# 12 roots +-sqrt(v_j), v_j roots of S(a v + b):  p_odd = 0,  p_{2m} = 2 A^m sum_i C(m,i) (-b)^(m-i) P_i,
# A = 1/a, P_i = power sums of the roots of S (top coefficients only).
# Usage: python3 e60.py <odd|plane|line1> <seed> [S=T6|gen] [p]
#   odd   : random tau, unknowns s,e1,e2,e3, equations k = 1,3,5,7  -> m = number of (s,z)
#   plane : tau = c0 + x c1 + y c2, unknowns x,y,s,A,b,e1,e2,e3, 8 equations -> deg H_S (x-eliminant)
# Writes a Singular script e60_<mode>_<seed>.sing and runs it.
import sys, random, subprocess
from math import comb
mode = sys.argv[1]; seed = int(sys.argv[2]); Sname = sys.argv[3] if len(sys.argv) > 3 else 'T6'
p = int(sys.argv[4]) if len(sys.argv) > 4 else 32003
random.seed(seed)
inv = lambda a: pow(a % p, p - 2, p)
if Sname == 'T6':
    P = [6, 0, 3, 0, 9 * inv(4) % p]
else:   # generic top part: random power sums P1..P4 of a sextic
    P = [6] + [random.randrange(p) for _ in range(4)]
R = lambda: random.randrange(1, p)
def zps(k):  # Singular expression list for power sums of z from e1,e2,e3
    return None
lines = []
if mode == 'odd':
    tau = [R() for _ in range(9)]
    lines.append("LIB \"elim.lib\";"); lines.append(f"ring r = {p},(s,e1,e2,e3),dp; option(redSB);")
    taus = '+'.join(f"({t}+s)^%d" for t in tau)
    ks = [1, 3, 5, 7]
elif mode == 'plane':
    c0 = [R() for _ in range(9)]; c1 = [R() for _ in range(9)]; c2 = [R() for _ in range(9)]
    lines.append("LIB \"elim.lib\";"); lines.append(f"ring r = {p},(x,y,s,A,b,e1,e2,e3),dp; option(redSB);")
    taus = '+'.join(f"({c0[i]}+{c1[i]}*x+{c2[i]}*y+s)^%d" for i in range(9))
    ks = list(range(1, 9))
lines.append("proc SAT(ideal J, ideal f) { def S = sat(J, f); if (typeof(S) == \"list\") { return(S[1]); } return(S); }")
lines.append("poly z1 = e1; poly z2 = e1*z1 - 2*e2; poly z3 = e1*z2 - e2*z1 + 3*e3;")
lines.append("list Z = z1, z2, z3;")
lines.append("int k; for (k = 4; k <= 8; k++) { Z = insert(Z, e1*Z[k-1] - e2*Z[k-2] + e3*Z[k-3], k-1); }")
eqs = []
for k in ks:
    rhs = "0"
    if k % 2 == 0:
        m = k // 2
        rhs = "2*A^%d*(%s)" % (m, '+'.join(f"{comb(m,i)*P[i] % p}*(-b)^{m-i}" for i in range(m + 1)))
    eqs.append(f"({taus % tuple([k]*taus.count('%d'))}) + Z[{k}] - ({rhs})")
lines.append("ideal I = " + ",\n".join(eqs) + ";")
if mode == 'odd':
    lines.append("ideal J = std(I); print(dim(J)); print(vdim(J));")
    lines.append("ideal Js = std(SAT(J, ideal(e3))); print(vdim(Js));")
    lines.append("ideal E = eliminate(J, e1*e2*e3); print(E);")
else:
    lines.append("ideal J = std(I); print(\"dim\"); print(dim(J)); print(vdim(J));")
    lines.append("ideal Js = std(SAT(J, ideal(A))); print(\"sat A\"); print(dim(Js)); print(vdim(Js));")
    lines.append("ideal E = eliminate(Js, y*s*A*b*e1*e2*e3); print(\"elim deg\"); print(deg(E[1])); print(size(E));")
    lines.append("print(factorize(E[1],2));")
lines.append("quit;")
fn = f"e60_{mode}_{seed}.sing"
open(fn, 'w').write("\n".join(lines) + "\n")
out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True)
print(out.stdout[-3000:], out.stderr[-1000:])
