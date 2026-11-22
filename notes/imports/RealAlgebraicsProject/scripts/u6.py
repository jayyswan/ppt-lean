# Session 15. Needs psl_group.py (written from psl_x8.py) next to it.
# Session 15: u6 = j6 - (symmetric sextic) with u6(x8 + t e) = c t^6 along all isotropic V4-eigencurves.
import sympy as sp, collections
exec(open('psl_group.py').read())
t = sp.symbols('t'); I = sp.I
def chi(al, v): return (-1) ** bin(al & v).count('1')
def curve(al, sgn=1):
    return [1 + t*chi(al, j) for j in range(4)] + [1 + sgn*I*t*chi(al, j) for j in range(4)] + [sp.Integer(-8)]
def p(k, x): return sum(xi**k for xi in x)
j6orb = orbit({0:1, 1:1, 2:1, 3:1, 4:2})
def j6(x): return sum(sp.Mul(*[x[i]**e for i, e in m]) for m in j6orb)
L = sp.symbols('l1:5')
def sym(x): return L[0]*p(2,x)**3 + L[1]*p(2,x)*p(4,x) + L[2]*p(3,x)**2 + L[3]*p(6,x)
eqs = []; data = {}
for al in (1, 2, 3):
    for sg in (1, -1):
        x = curve(al, sg)
        P = sp.Poly(sp.expand(j6(x) - sym(x)), t)
        data[(al, sg)] = P
        for k in (0, 2, 4):
            c = P.coeff_monomial(t**k); eqs += [sp.re(c), sp.im(c)]
sol = sp.solve([e for e in eqs if e != 0], L, dict=True)
print('solutions:', sol)
for s in sol:
    for key, P in data.items():
        print(key, sp.factor(P.subs(s).as_expr()))
