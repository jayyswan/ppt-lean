import numpy as np, sympy as sp
exec(open('pencil_flex.py').read().split("if __name__")[0])
rs = np.random.default_rng(3)
lam = sp.Rational(int(rs.integers(1, 9)), int(rs.integers(1, 5)))
u = [sp.Integer(int(rs.integers(-5, 6))) for _ in range(2)]
vv = [sp.Integer(int(rs.integers(-5, 6))) for _ in range(4)]
U = T**3 + u[0]*T + u[1]; V = vv[0]*T**3 + vv[1]*T**2 + vv[2]*T + vv[3]
X, Y = sp.symbols('X Y')
Gam = sp.resultant(X - U, Y - V, T)
Gh = sp.expand(sp.Poly(Gam, X, Y).homogenize(z).as_expr().subs({X: x, Y: y}))
Eh = x**3 + lam*x**2*z + y**2*z
ra, rb = make_restrictor(Eh), make_restrictor(Gh)
print("lam", lam, "U", U, "V", V)
M = matrix(ra, rb, 0, 0); print(np.round(M.real,4)); print("minors", np.abs(minors(M)).max())
for e in [1e-2,1e-3,1e-4]:
    print(e, np.linalg.norm(residual(ra, rb, np.array([e, 0.7*e], dtype=complex))))
