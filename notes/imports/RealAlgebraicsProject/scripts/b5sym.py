# Session 62: row B5 (Bezier (t^2, cubic) x Q-quintic graph) -- exact algebra.
# Checks: (1) with e1=e3=e5=0 the 10-root polynomial is E(w^2)+R(w), E monic quintic, R odd cubic;
# (2) the depressed coefficients B3, B2 of E in power sums (Newton, odd p's = 0);
# (3) planted identity: y=(v+s, zeta) in L135^(10) <=> v is a crossing parameter set.
import sympy as sp
p = sp.symbols('p1:11')
e = [sp.Integer(1)]
for k in range(1, 11):  # Newton: k e_k = sum_{i=1}^k (-1)^{i-1} e_{k-i} p_i
    e.append(sp.expand(sum((-1)**(i-1)*e[k-i]*p[i-1] for i in range(1, k+1))/k))
sub = {p[0]: 0, p[2]: 0, p[4]: 0}
E = {k: sp.expand(e[k].subs(sub)) for k in range(11)}
B3 = sp.expand(E[4] - sp.Rational(2, 5)*E[2]**2)
B2 = sp.expand(E[6] - sp.Rational(3, 5)*E[2]*E[4] + sp.Rational(4, 25)*E[2]**3)
print('e2 =', E[2], '  e4 =', E[4])
print('B3 =', sp.factor(B3))
print('B2 =', sp.factor(B2))
# depressing check with a generic monic quintic
V, a2, a4, a6, y = sp.symbols('V a2 a4 a6 y')
Q = sp.expand((y - a2/5)**5 + a2*(y - a2/5)**4 + a4*(y - a2/5)**3 + a6*(y - a2/5)**2)
print('depressed y^4:', Q.coeff(y, 4), ' y^3 - B3:', sp.simplify(Q.coeff(y, 3) - (a4 - sp.Rational(2, 5)*a2**2)),
      ' y^2 - B2:', sp.simplify(Q.coeff(y, 2) - (a6 - sp.Rational(3, 5)*a2*a4 + sp.Rational(4, 25)*a2**3)))
# planted numeric identity
import numpy as np
rng = np.random.default_rng(1)
def ps(z, k): return np.sum(z**k)
def F(z):
    return np.array([ps(z, 1), ps(z, 3), ps(z, 5)])
z = rng.normal(size=10)
for it in range(60):
    J = np.array([[k*zi**(k-1) for zi in z] for k in (1, 3, 5)])
    z = z - np.linalg.pinv(J) @ F(z)
print('real 10-point set in L135^(10): residual', np.abs(F(z)).max())
c = np.poly(z)  # w^10 - e1 w^9 + ...
print('odd coefficients w^9,w^7,w^5:', c[1], c[3], c[5])
zeta = z[-1]; v = z[:-1]
w = sp.symbols('w')
chi = np.poly(v)
prod = np.polymul(chi, [1, -zeta])
print('chi_v(w)(w-zeta) - F10 max diff:', np.abs(prod - c).max())
