"""Session 12: the symmetric sextic h6 vanishing on the (4,4,1) plane Pi, and its local data.

Pi = {(a,a,a,a, b,b,b,b, c) : c = -4(a+b)}.  Normal space N = V/Pi = std(set1) + std(set2),
n = (u_1..u_4, v_1..v_4, 0) with sum u = sum v = 0.  We compute the order of vanishing of h6
along Pi and its normal form, and the values of the radicands at V4-eigenvectors.
"""
import sympy as sp

x = sp.symbols('x0:9')
def p(k, v=x): return sum(t**k for t in v)
c1, c2, c3, c4 = sp.symbols('c1:5')
a, b = sp.symbols('a b')
Pi = [a] * 4 + [b] * 4 + [-4 * (a + b)]
gen = c1 * p(2)**3 + c2 * p(2) * p(4) + c3 * p(6) + c4 * p(3)**2
onPi = sp.Poly(sp.expand(gen.subs(dict(zip(x, Pi)))), a, b)
sol = sp.solve(onPi.coeffs(), [c1, c2, c3, c4], dict=True)[0]
h6 = sp.expand(gen.subs(sol))
free = [s for s in (c1, c2, c3, c4) if s in h6.free_symbols]
h6 = sp.expand(h6.subs({free[0]: 1}))
h6 = sp.expand(h6 / sp.gcd_terms(h6).as_coeff_Mul()[0]) if False else h6
P2, P3, P4, P6 = sp.symbols('p2 p3 p4 p6')
h6p = sp.expand((c1 * P2**3 + c2 * P2 * P4 + c3 * P6 + c4 * P3**2).subs(sol).subs({free[0]: 1}))
den = sp.lcm([sp.fraction(t)[1] for t in sp.Add.make_args(h6p)])
h6p = sp.expand(h6p * den)
g = sp.gcd([t.as_coeff_Mul()[0] for t in sp.Add.make_args(h6p)])
h6p = sp.expand(h6p / g)
print("h6 =", h6p)
H6 = lambda v: h6p.subs({P2: p(2, v), P3: p(3, v), P4: p(4, v), P6: p(6, v)})

# local expansion along Pi: x = x0 + e*n with n normal
e = sp.symbols('e')
u = sp.symbols('u1:5'); w = sp.symbols('w1:5')
n = list(u) + list(w) + [0]
cons = {u[3]: -(u[0] + u[1] + u[2]), w[3]: -(w[0] + w[1] + w[2])}
pt = [Pi[i] + e * n[i] for i in range(9)]
ser = sp.expand(H6(pt).subs(cons))
ser_poly = sp.Poly(ser, e)
for k in range(0, 5):
    ck = sp.factor(ser_poly.coeff_monomial(e**k))
    print(f"order e^{k} coefficient:", ck if k < 3 else ("0" if ck == 0 else "nonzero"))
