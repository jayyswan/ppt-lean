# S67.3(d): projection of X = {Tr y = Tr y^3 = 0} from the node N = (1^5,(-1)^5).
# For v with Tr v = 0: third point y = c N - q v (c = Tr v^3, q = 3 Tr(N v^2)) lies on X, and
# Tr y^5 = q^3 * (-(20/3) c^3 + 5 c q Tr(N v^4) - q^2 Tr v^5).  Numerical check.
import numpy as np
rng = np.random.default_rng(1)
N = np.array([1.]*5 + [-1.]*5)
for trial in range(5):
    v = rng.normal(size=10) + 1j*rng.normal(size=10); v -= v.mean()
    c = np.sum(v**3); q = 3*np.sum(N*v**2); T4 = np.sum(N*v**4); T5 = np.sum(v**5)
    y = c*N - q*v
    lhs = np.sum(y**5); rhs = q**3*(-(20/3)*c**3 + 5*c*q*T4 - q**2*T5)
    print('Tr y =', abs(np.sum(y)) < 1e-9, ' Tr y^3 =', abs(np.sum(y**3))/abs(c)**3 < 1e-9, ' rel. error of identity:', abs(lhs-rhs)/abs(lhs))
