"""B4-01: implicit degree of the offset of the parabola y = x^2 by d.

Rational reparametrization by s = 2t + sqrt(1+4t^2):
    X = ((s^2-1)/(4s)) * (1 - 4 d s/(s^2+1))
    Y = ((s^2-1)/(4s))^2 + 2 d s/(s^2+1)
Clear denominators and eliminate s. Confirms O5's 4n-2 = 6 and A4's implicit degree 6.

Run: C:\\Users\\jason\\AppData\\Local\\Programs\\Python\\Python312\\python.exe B4-01-parabola-offset-degree.py
"""
import sympy as sp

s, X, Y, d, t = sp.symbols("s X Y d t")

# X and Y as rational functions of s, written over a common denominator.
exprX = ((s**2 - 1) / (4 * s)) * (1 - 4 * d * s / (s**2 + 1))
exprY = ((s**2 - 1) / (4 * s)) ** 2 + 2 * d * s / (s**2 + 1)

# Clear denominators: nX = 0 and nY = 0 are polynomial in s with coefficients in X, Y, d.
nX = sp.together(exprX - X).as_numer_denom()[0]
nY = sp.together(exprY - Y).as_numer_denom()[0]
nX = sp.expand(nX)
nY = sp.expand(nY)

r = sp.resultant(nX, nY, s)
r = sp.factor(r)
print("factorization:", r)

# Total (X,Y) degree of the nondegenerate factor.
poly = sp.Poly(r, X, Y)
# Drop the constant and pure-d factors; find the factor with positive XY degree.
for fac, _ in sp.factor_list(r)[1]:
    p = sp.Poly(fac, X, Y)
    if p.total_degree() > 0:
        print("main factor total (X,Y) degree:", p.total_degree())
        print("  degree in X:", sp.degree(fac, X), " degree in Y:", sp.degree(fac, Y))
        print("  monomials of top total degree:",
              sorted(sp.Poly(fac, X, Y).monoms(), key=lambda m: -sum(m))[:6])
