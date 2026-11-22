# e60r.py -- session 60: reduced plane-slice system for H_S (row E, fixed sextic S, P dials).
# Unknowns x,y (plane tau = c0 + x c1 + y c2), s (shift), A = 1/alpha, b = beta; e1,e2,e3 of the
# cubic cofactor are eliminated by the k = 1,2,3 power-sum equations (linear in e1,e2,e3).
# Usage: python3 e60r.py <seed> <sing|msolve> [S=T6|gen|<P1,P2,P3,P4>] [p]
# Writes e60r_<seed>.sing or e60r_<seed>.ms and runs it; prints dim / vdim / eliminant degree (Singular)
# or the msolve output head.
import sys, random, subprocess
from math import comb
seed = int(sys.argv[1]); tool = sys.argv[2]; Sname = sys.argv[3] if len(sys.argv) > 3 else 'T6'
p = int(sys.argv[4]) if len(sys.argv) > 4 else 32003
random.seed(seed)
inv = lambda a: pow(a % p, p - 2, p)
if Sname == 'T6': P = [6, 0, 3, 0, 9 * inv(4) % p]
elif Sname == 'gen': P = [6] + [random.randrange(p) for _ in range(4)]
else: P = [6] + [int(v) % p for v in Sname.split(',')]
R = lambda: random.randrange(1, p)
import os
EVEN = os.environ.get('EVEN', '0') == '1'
VARORDER = os.environ.get('ORDER', 'x,y,s,A,b')
c0 = [R() for _ in range(9)]; c1 = [R() for _ in range(9)]; c2 = [R() for _ in range(9)]
import sympy as sp
x, y, s, A, b = sp.symbols('x y s A b')
w = [c0[i] + c1[i]*x + c2[i]*y + s for i in range(9)]
def tgt(k):
    if k % 2: return sp.Integer(0)
    m = k // 2
    if EVEN:  # S even (P1 = P3 = 0): use invariants A := alpha^-2, b := alpha^-1 beta (sign symmetry removed)
        return 2*sum(comb(m, 2*j)*P[2*j]*A**j*(-b)**(m - 2*j) for j in range(m//2 + 1))
    return 2*A**m*sum(comb(m, i)*P[i]*(-b)**(m - i) for i in range(m + 1))
pw = [None] + [sp.expand(sum(wi**k for wi in w)) for k in range(1, 9)]
Zt = [None] + [sp.expand(tgt(k) - pw[k]) for k in range(1, 9)]   # required power sums of z
# Newton for 3 variables: p1 = e1, p2 = e1 p1 - 2 e2, p3 = e1 p2 - e2 p1 + 3 e3
inv2, inv3 = sp.Rational(1, 2), sp.Rational(1, 3)
e1 = Zt[1]; e2 = sp.expand((e1*Zt[1] - Zt[2])*inv2); e3 = sp.expand((Zt[3] - e1*Zt[2] + e2*Zt[1])*inv3)
Z = [None, Zt[1], Zt[2], Zt[3]]
for k in range(4, 9): Z.append(sp.expand(e1*Z[k-1] - e2*Z[k-2] + e3*Z[k-3]))
eqs = [sp.expand(Z[k] - Zt[k]) for k in range(4, 9)]
def modp(e):
    P_ = sp.Poly(e, x, y, s, A, b)
    terms = []
    for mon, co in P_.terms():
        num, den = sp.fraction(sp.Rational(co))
        c = int(num) * inv(int(den)) % p
        if c: terms.append((c, mon))
    return terms
def tostr(terms, vars_=('x','y','s','A','b')):
    out = []
    for c, mon in terms:
        m = '*'.join(f"{v}^{e}" for v, e in zip(vars_, mon) if e)
        out.append(f"{c}*{m}" if m else f"{c}")
    return '+'.join(out)
E = [tostr(modp(e)) for e in eqs]
if tool == 'sing':
    L = ['LIB "elim.lib";', f"ring r = {p},(x,y,s,A,b),dp; option(redSB);",
         "proc SAT(ideal J, ideal f) { def S = sat(J, f); if (typeof(S) == \"list\") { return(S[1]); } return(S); }",
         "ideal I = " + ",\n".join(E) + ";", "ideal J = std(I); print(\"dim vdim\"); print(dim(J)); print(vdim(J));",
         "ideal Js = std(SAT(J, ideal(A))); print(\"sat A\"); print(dim(Js)); print(vdim(Js));",
         "ideal El = eliminate(Js, y*s*A*b); print(\"elim deg\"); print(deg(El[1]));",
         "print(factorize(El[1], 2));", "quit;"]
    fn = f"e60r_{seed}.sing"; open(fn, 'w').write("\n".join(L) + "\n")
    out = subprocess.run(["Singular", "-q", fn], capture_output=True, text=True)
    print(out.stdout[-4000:], out.stderr[-1000:])
else:
    fn = f"e60r_{seed}.ms"
    open(fn, 'w').write(VARORDER + "\n%d\n" % p + ",\n".join(E) + "\n")
    out = subprocess.run(["msolve", "-f", fn, "-o", fn + ".out", "-t", "1"], capture_output=True, text=True)
    print(out.stdout[-3000:], out.stderr[-2000:]); print(open(fn + ".out").read()[:3000])
