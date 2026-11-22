# Exact check: on trace-zero z, Q5(z) = (3/4) * dQ4_z(xi), xi = z^2 - Tr(z^2)/9 (projection of z^2 to trace zero).
import sympy as sp
z = sp.symbols('z0:9'); sub = {z[0]: -sum(z[1:])}
p = lambda k, v=z: sum(c**k for c in v)
Q4 = 6*p(4) - p(2)**2; Q5 = 18*p(5) - 5*p(2)*p(3)
xi = [c**2 - p(2)/9 for c in z]
dQ4 = sum(sp.diff(Q4, z[i])*xi[i] for i in range(9))
print('identity holds on V:', sp.expand((Q5 - sp.Rational(3, 4)*dQ4).subs(sub)) == 0)
# also: without the projection the identity fails by 18 p3 * Tr-part; check dQ4(1) = 24 p3 on V
print('dQ4(1) = 24 p3 on V:', sp.expand((sum(sp.diff(Q4, c) for c in z) - 24*p(3)).subs(sub)) == 0)
