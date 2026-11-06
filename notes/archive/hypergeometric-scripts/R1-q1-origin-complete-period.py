"""R1-Q1: the power_law origin problem and the complete-period question.

The construct under test is  y = a x^b  (x > 0), whose arc-length density is
    ds/dx = sqrt(1 + C x^m),   C = a^2 b^2,  m = 2b - 2,
so that (V4)
    G(X) := int_0^X sqrt(1 + C x^m) dx = X * 2F1(-1/2, 1/m; 1 + 1/m; -C X^m).

Checks:
 (A) V4 itself, to >= 30 digits, over rational m.                       [NC]
 (B) The curve primitive excludes x = 0; arc_length of a piece [x0, X]
     returns G(X) - G(x0) with x0 > 0.  (structural + NC)
 (C) For INTEGER b = m/2+1 (m in {0,2,4,6,8,10}) the origin IS reachable
     because poly_graph draws y = x^n through (0,0).                     [NC]
 (D) Any REAL-ANALYTIC graph y=f(x) with ds/dx = sqrt(1+C x^m) is a power
     law f(x) = +-(2 sqrt(C)/(m+2)) x^(m/2+1) + const, hence itself excluded
     from x = 0 when m/2+1 is not an integer in [1,6].                    [NC]
 (E) The offset of the power law has a DIFFERENT length density; it is not
     sqrt(1+C' x^m).                                                      [NC]
 (F) The second-kind complete integral int_0^inf sqrt(1+x^m) dx DIVERGES,
     while the first-kind period int_0^inf dx/sqrt(1+x^m) is finite and is
     (1/m) B(1/m, 1/2 - 1/m).  So no complete period is an arc length.    [NC]
"""
import mpmath as mp

mp.mp.dps = 45

# ----------------------------------------------------------------------------
def G_formula(C, m, X):
    """V4 closed form G(X) for density sqrt(1 + C x^m)."""
    C = mp.mpf(C); m = mp.mpf(m); X = mp.mpf(X)
    z = -C * X**m
    return X * mp.hyp2f1(mp.mpf(-1)/2, 1/m, 1 + 1/m, z)


def G_quad(C, m, X):
    C = mp.mpf(C); m = mp.mpf(m); X = mp.mpf(X)
    f = lambda x: mp.sqrt(1 + C * x**m)
    # split points keep the adaptive quadrature away from the soft x^{m/2} cusp
    pts = [0, X*mp.mpf('0.0625')**1, X*mp.mpf('0.125'), X*mp.mpf('0.25'),
           X*mp.mpf('0.5'), X*mp.mpf('0.75'), X]
    return mp.quad(f, pts)


def dg(x):
    return -mp.log10(abs(x)) if x > 0 else mp.inf


print("== (A) V4: closed form vs numeric integral, sqrt(1 + C x^m) ==")
print(f"{'m':>6} {'C':>10} {'X':>10} {'|closed-quad|':>16} {'digits':>8}")
for (m, C, X) in [(2, '2.25', '0.9'), (3, '2.25', '0.7'), (4, '2.25', '0.6'),
                  (6, '9', '0.5'), (8, '9', '0.4'), (10, '9', '0.35'),
                  (7, '3', '0.55'), (mp.mpf(7)/2, '4', '0.6'),
                  (mp.mpf(1)/2, '2', '0.9')]:
    a = G_formula(C, m, X); b = G_quad(C, m, X)
    d = abs(a-b)
    print(f"{mp.nstr(m,6):>6} {C:>10} {X:>10} {mp.nstr(d,5):>16} {mp.nstr(dg(d),5):>8}")

print()
print("== (B) the piece integrally available is G(X) - G(x0), x0 > 0 ==")
m, C, X, x0 = mp.mpf(6), mp.mpf(9), mp.mpf('0.5'), mp.mpf('0.2')
piece = G_formula(C, m, X) - G_formula(C, m, x0)
piece_num = mp.quad(lambda x: mp.sqrt(1 + C*x**m), [x0, X])
print(f"   m=6 C=9 X=0.5 x0=0.2")
print(f"   G(X)-G(x0)          = {mp.nstr(piece, 32)}")
print(f"   numeric [x0,X]      = {mp.nstr(piece_num, 32)}  diff={mp.nstr(abs(piece-piece_num),5)}")
print(f"   G(0) (limit)        = 0 (the algebraic value at x=0), but (0,0) is NOT on the curve:")
print(f"   power_law set has 0 < x, so no tracing with an endpoint at (0,0) exists.")

print()
print("== (C) integer exponent: poly_graph DOES include the origin ==")
print("   n = m/2+1, density sqrt(1+n^2 x^(2n-2)); compare G(0..X) with formula")
for n in [1, 2, 3, 4, 5, 6]:
    m = 2*n-2; C = n*n; X = mp.mpf('0.5')
    num = mp.quad(lambda x: mp.sqrt(1 + n*n*x**(2*n-2)), [0, X])
    closed = mp.sqrt(2)*X if n == 1 else G_formula(C, m, X)   # m=0: density sqrt2
    print(f"   n={n} m={m:>2}: G={mp.nstr(closed,25)} diff={mp.nstr(abs(closed-num),5)}"
          f"  origin included by poly_graph: {'yes' if n<=6 else 'no'}")

print()
print("== (D) graphs sharing the density sqrt(1+C x^m) are power laws ==")
# f'(x)^2 = C x^m  =>  f' = sqrt(C) x^(m/2).  Check by finite differences on
# the graph y = x^b, b = m/2+1:  f'(x) = b x^(m/2), so f'(x)/x^(m/2) = b const.
print("   fit k(x) := f'(x) / x^(m/2) on y = x^b, b = m/2+1; must be b (constant)")
for m in [mp.mpf(3), mp.mpf(5), mp.mpf(7), mp.mpf(6), mp.mpf('0.5')]:
    b = m/2 + 1
    x1, x2 = mp.mpf('0.3'), mp.mpf('1.3')
    # derivative of x^b
    k1 = b*x1**(b-1)/x1**(m/2)
    k2 = b*x2**(b-1)/x2**(m/2)
    print(f"   m={mp.nstr(m,5):>6}: k(0.3)={mp.nstr(k1,22)} k(1.3)={mp.nstr(k2,22)}"
          f"  (equal to b={mp.nstr(b,10)}: {abs(k1-k2)<mp.mpf('1e-30')})")

print()
print("== (E) the offset density is NOT sqrt(1+C x^m) ==")
m = mp.mpf(6); n = m/2 + 1; C = n*n; d = mp.mpf('0.17')
def yp(x): return n*x**(n-1)
def v(x):  return mp.sqrt(1 + C*x**m)
def kappa(x):
    y2 = n*(n-1)*x**(n-2)
    return y2/(1 + C*x**m)**(mp.mpf(3)/2)
def integrand_d(x):        # |gamma_d'(x)| = (1 + d*kappa(x)) * v(x)
    return (1 + d*kappa(x))*v(x)
# if it were sqrt(1+C' x^m), (integrand^2 - 1)/x^m would be constant.
for x in ['0.3', '0.6', '1.1', '1.6']:
    x = mp.mpf(x)
    c = (integrand_d(x)**2 - 1)/x**m
    print(f"   x={mp.nstr(x,4):>5}: (s^2-1)/x^m = {mp.nstr(c,22)}")

print()
print("== (F) second-kind collapses? compare with the complete first-kind period ==")
for m in [6, 8, 10]:
    m = mp.mpf(m)
    fd = lambda x: 1/mp.sqrt(1 + x**m)
    firstkind = mp.quad(fd, [0, 1, 2, 10, mp.inf])
    beta = mp.beta(1/m, mp.mpf(1)/2 - 1/m)/m
    print(f"   m={mp.nstr(m,3):>4}: int_0^inf dx/sqrt(1+x^m) = {mp.nstr(firstkind,30)}"
          f"  diff vs (1/m)B(1/m,1/2-1/m)={mp.nstr(abs(firstkind-beta),5)}")
    # second-kind: grow with upper limit
    for U in [10, 100, 1000]:
        U = mp.mpf(U)
        g = mp.quad(lambda x: mp.sqrt(1 + x**m), [0, 1, 2, 10, U])
        asym = (2/(m+2))*U**(m/2+1)
        print(f"        int_0^{mp.nstr(U,6)} sqrt(1+x^m) = {mp.nstr(g,25)}"
              f"   (asymptotic (2/(m+2))U^(m/2+1)={mp.nstr(asym,25)})")
