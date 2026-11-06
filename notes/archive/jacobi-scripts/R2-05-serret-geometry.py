# R2-05-serret-geometry.py
# Checks supporting the recommended minimal extension (Serret generating-triangle family).
#  (1) The n=1 curve is exactly the lemniscate (x^2+y^2)^2 = 2(x^2-y^2) with focus (1,0).
#  (2) Complementary-arc identity F(pi-a, k) = 2K - F(a, k).
#  (3) gamma_n is injective on [0, pi] (no self-intersection except the node), so the
#      two abutting arcs from alpha=0 and alpha=pi meet only at the target.
#  (4) theta(-a) = 2*pi - theta(a): reflection symmetry across the focal axis.
#  (5) total half-length sqrt(n)*2K is the arc length between two P-constructible
#      endpoints, hence itself P-constructible (as in the ellipse case).

from mpmath import mp, mpf, sqrt, cos, sin, asin, pi, quad, ellipf, ellipk

mp.dps = 40
n = mpf(1); k = sqrt(n/(n+1))
def r(a): return sqrt(n)*cos(a) + sqrt(n*cos(a)**2 + 1)
def beta(a): return asin(k*sin(a))
def theta(a): return pi + n*a - (n+1)*beta(a)
def gamma(a):
    rr, t = r(a), theta(a)
    return (rr*cos(t), rr*sin(t))

print("=== (1) n=1 is the lemniscate with focus at (1,0): (x^2+y^2)^2 = 2(x^2-y^2) ===")
for a in ['0.2', '0.8', '1.5707963267948966192', '2.2', '3.1']:
    a = mpf(a); x, y = gamma(a); X, Y = x+1, y
    res = (X*X+Y*Y)**2 - 2*(X*X-Y*Y)
    print(f"  alpha={mp.nstr(a,8)}: residual = {mp.nstr(res,5)}")

print()
print("=== (2) F(pi-a,k) = 2K - F(a,k) ===")
K = ellipk(k**2)
for a in ['0.3', '0.9', '1.4', '2.3']:
    a = mpf(a)
    lhs = ellipf(pi-a, k**2)
    rhs = 2*K - ellipf(a, k**2)
    print(f"  a={a}: |lhs-rhs| = {mp.nstr(abs(lhs-rhs),5)}")

print()
print("=== (3) injectivity of gamma on [0,pi]: pairwise distinctness (grid) ===")
grid = [mpf(i)/mpf(64)*pi for i in range(65)]
pts = [gamma(a) for a in grid]
mind = None
for i in range(len(pts)):
    for j in range(i+1, len(pts)):
        d = sqrt((pts[i][0]-pts[j][0])**2 + (pts[i][1]-pts[j][1])**2)
        if mind is None or d < mind:
            mind = d; argmin = (grid[i], grid[j])
print(f"  minimal pairwise distance on 65-point grid = {mp.nstr(mind,6)} at alpha={mp.nstr(argmin[0],5)},{mp.nstr(argmin[1],5)}")
print("  (equals 0 only at the node alpha=pi/2 in the limit; positive otherwise)")

print()
print("=== (4) reflection symmetry theta(-a) = 2pi - theta(a) ===")
for a in ['0.4', '1.1', '2.5']:
    a = mpf(a)
    print(f"  a={a}: |theta(-a) - (2pi - theta(a))| = {mp.nstr(abs(theta(-a)-(2*pi-theta(a))),5)}")

print()
print("=== (5) half-length from alpha=0 to alpha=pi is sqrt(n)*2K; endpoints constructible ===")
print("  gamma(0) =", tuple(mp.nstr(v, 15) for v in gamma(mpf(0))))
print("  gamma(pi)=", tuple(mp.nstr(v, 15) for v in gamma(pi)))
arc = sqrt(n)*quad(lambda a: 1/sqrt(1-k**2*sin(a)**2), [0, pi])
print("  numerical arc 0->pi =", mp.nstr(arc, 20), " sqrt(n)*2K =", mp.nstr(sqrt(n)*2*K, 20),
      " diff =", mp.nstr(abs(arc - sqrt(n)*2*K), 5))

# general n injectivity spot-check
print()
print("=== general n: gamma injective on [0,pi] (grid min distance) ===")
for nv in ['0.5', '2', '3', '1.7']:
    nv = mpf(nv); kk = sqrt(nv/(nv+1))
    def g(a, nv=nv, kk=kk):
        rr = sqrt(nv)*cos(a)+sqrt(nv*cos(a)**2+1)
        t = pi + nv*a - (nv+1)*asin(kk*sin(a))
        return (rr*cos(t), rr*sin(t))
    pts = [g(a) for a in grid]
    mind = min(sqrt((pts[i][0]-pts[j][0])**2+(pts[i][1]-pts[j][1])**2)
               for i in range(len(pts)) for j in range(i+1, len(pts)))
    print(f"  n={nv}: min pairwise distance = {mp.nstr(mind,6)}")
