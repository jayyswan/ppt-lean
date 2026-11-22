# Session 39: the curve X_h = {G(x;U)=0} for fixed h = x^3+a*x+b (a,b rational).
# Prints: degree of G in x,U; factorization of disc_x(G) as a polynomial in U (with multiplicities);
# the geometric genus via PARI's genus routine is not available, so we print the data for Riemann-Hurwitz.
# usage: python3 xh_disc.py a b
import sys, cypari; P = cypari.pari
P.allocatemem(2*10**9)
for l in open('EngineO.gp'):
    l = l.strip()
    if l and not l.startswith('\\\\'): P(l)
a, b = sys.argv[1], sys.argv[2]
P(f'Gh=substvec(G,[a,b],[({a}),({b})]); Bh=substvec(Bu,[a,b],[({a}),({b})]); Ah=substvec(Au,[a,b],[({a}),({b})])')
print('deg_x', P('poldegree(Gh,x)'), 'deg_U', P('poldegree(Gh,U)'))
print('content in x (gcd of coeffs, poly in U):', P('content(Gh)'))
print('irreducible over Q(U)?', P('polisirreducible(Gh)'))
P('D=poldisc(Gh,x)')
print('deg_U disc', P('poldegree(D,U)'))
f = P('factor(D)')
print('factorization of disc_x(G) in Q[U]:')
for i in range(len(f[0])):
    p = f[0][i]; m = f[1][i]
    print('  mult', m, ' deg', P('poldegree')(p), '  ', str(p)[:200])
print('Bh =', P('factor(Bh)'))
print('Ah =', P('factor(Ah)'))
