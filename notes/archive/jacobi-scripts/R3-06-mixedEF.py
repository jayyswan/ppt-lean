"""
R3 script 06:
 (A) Decisive test of the "mixed E/F at different moduli" loophole: is E_{c'}(am_c(u))
     expressible as  A*E_c(am_c) + B*u + R(sin(am_c))  with R rational?  Test the derivative
     form (dagger) by an overdetermined linear fit.  Sanity checks: c'=c (A=1,B=0,R'=0) and
     c'=0 (A=B=0, R'(s)=1) must fit exactly.
 (B) third-kind elementarity for special n (sympy).
Convention: parameter m=k^2.
"""
from mpmath import mp, mpf, ellipf, ellipe, sqrt, sin, cos, pi, findroot
import mpmath as mpm

mp.dps = 40


def F(phi, k):
    return ellipf(phi, k ** 2)


def am(u, k):
    return findroot(lambda ph: F(ph, k) - u, u, tol=mpf('1e-38'))


def test_relation(c, cp, npts=14, sdeg=3):
    """Fit  sqrt((1-c' s^2)(1-c s^2)) = A(1-c s^2)+B+sum_{j<=sdeg} p_j s^j sqrt((1-s^2)(1-c s^2))."""
    k = sqrt(c)
    us = [mpf(str(0.15 + 0.11 * i)) for i in range(npts)]
    rows, ycol = [], []
    for u in us:
        s = sin(am(u, k))
        base = sqrt((1 - s ** 2) * (1 - c * s ** 2))
        row = [1 - c * s ** 2, mpf(1)]
        for j in range(sdeg + 1):
            row.append(s ** j * base)
        rows.append(row)
        ycol.append(sqrt((1 - cp * s ** 2) * (1 - c * s ** 2)))
    M = mpm.matrix(rows)
    y = mpm.matrix(ycol)
    sol = mpm.lu_solve(M.T * M, M.T * y)
    resid = max(abs(y[i] - sum(sol[j] * rows[i][j] for j in range(len(sol))))
                for i in range(len(ycol)))
    return sol, resid


print("== (A) mixed E/F: fit (dagger) overdetermined (14 pts, 5 params) ==")
for c in [mpf('0.09'), mpf('0.49')]:
    for cp, tag in [(c, "c'=c (sanity: expect A=1,B=0,p=0)"),
                    (mpf(0), "c'=0 (sanity: expect A=0,B=0,p0=1)"),
                    (1 - c, "c'=1-c (isomorphic Legendre curve!)"),
                    (c / 2, "c'=c/2 (generic)"),
                    (mpf('0.25'), "c'=0.25 (generic)")]:
        sol, resid = test_relation(c, cp)
        print(f"c={mp.nstr(c,4)} {tag}: A={mp.nstr(sol[0],8)} B={mp.nstr(sol[1],8)} "
              f"p=({mp.nstr(sol[2],6)},{mp.nstr(sol[3],6)},{mp.nstr(sol[4],6)},{mp.nstr(sol[5],6)}) "
              f"resid={mp.nstr(resid,4)}")

print()
print("== (B) third-kind: is Pi(phi,n,k) elementary for special n? (sympy) ==")
RUN_B = False
if RUN_B:
    import sympy as sp
    x, kk, n = sp.symbols('x k n', positive=True)
    integrand = 1 / ((1 + n * sp.sin(x) ** 2) * sp.sqrt(1 - kk ** 2 * sp.sin(x) ** 2))
    for nval in [0, 1, -1, kk ** 2, -kk ** 2, 1 - kk ** 2, 1 / kk ** 2]:
        expr = sp.simplify(integrand.subs(n, nval))
        try:
            res = sp.integrate(expr, x)
            has_elliptic = any(fn in str(res) for fn in ['elliptic', 'Elliptic', 'hypergeom'])
            print(f"n={nval}: elementary={not has_elliptic}  result_type={str(res)[:60]}")
        except Exception as e:
            print(f"n={nval}: integrate failed ({type(e).__name__})")
