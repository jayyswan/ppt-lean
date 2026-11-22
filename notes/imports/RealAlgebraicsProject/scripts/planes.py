# Lemma F.2 check: for k-planes with orthonormal frame, Q4 = 0 forces sum|x_j|^4 = k(k+2)/18;
# Cauchy-Schwarz needs >= k^2/9, impossible for k >= 3.  Verify the double-Laplacian constants symbolically.
import sympy as sp, numpy as np
for k in (2,3,4):
    l=sp.symbols(f'l1:{k+1}'); x=sp.symbols(f'x1:{k+1}')
    lap=lambda f: sum(sp.diff(f,v,2) for v in l)
    a=sp.expand(sum(xi*li for xi,li in zip(x,l))**4); b=sp.expand(sum(li**2 for li in l)**2)
    print(k, sp.factor(lap(lap(a))), lap(lap(b)), ' => sum|x|^4 =', sp.Rational(lap(lap(b)),6*24), ' CS bound', sp.Rational(k*k,9))
