"""R1-Q3 (B6): hyperelliptic periods of y^2 = 1 + x^m, m = 6, 8, 10.

Complete (first-kind, holomorphic) periods of y^2 = 1 + x^m:
    int_0^inf x^(p-1) / (1+x^m)^(1/2) dx = (1/m) B(p/m, 1/2 - p/m),  p = 1..m/2-1.
The arc length of the graph y = x^(m/2+1) is the SECOND-kind differential
    int sqrt(1+x^m) dx,
which diverges at infinity; its incomplete value at X is a 2F1.

Checks:
 (A) the Beta/Bohr formula above, >= 30 digits.                          [NC]
 (B) the Gamma products, and which denominators are new vs Gamma.lean.   [NC]
 (C) the second-kind integral diverges; no finite "complete" value.      [NC]
 (D) a cubic Bezier's speed^2 is a quartic (genus 1); a degree-d poly graph
     has speed^2 of degree 2d-2 (genus up to 4 at d=6).                  [NC]
 (E) the number of independent holomorphic periods: genus g has g of them,
     so the genus-1 "solve for F using E" trick the repo uses has no genus-2
     analogue. (structural, classical)
 (F) the incomplete arclength G(X) is NOT a Beta value: it varies continuously
     and equals no Beta period at X = the natural "closing" points.       [NC]
"""
import mpmath as mp

mp.mp.dps = 40


def dg(x):
    return -mp.log10(abs(x)) if x > 0 else mp.inf


print("== (A) complete first-kind periods (1/m)B(p/m, 1/2 - p/m) vs numeric ==")
print(f"{'m':>4} {'p':>3} {'B-period':>28} {'|num-formula|':>14} {'digits':>8}")
for m in [6, 8, 10]:
    for p in range(1, m//2):
        beta = mp.beta(mp.mpf(p)/m, mp.mpf(1)/2 - mp.mpf(p)/m)/m
        num = mp.quad(lambda x: x**(p-1)/mp.sqrt(1+x**m), [0, 1, 2, 10, mp.inf])
        d = abs(num-beta)
        print(f"{m:>4} {p:>3} {mp.nstr(beta,28):>28} {mp.nstr(d,5):>14} {mp.nstr(dg(d),5):>8}")

print()
print("== (B) Gamma products and denominator inventory ==")
new = set()
for m in [6, 8, 10]:
    print(f"   m = {m}:")
    seen = set()
    for p in range(1, m//2):
        beta = mp.beta(mp.mpf(p)/m, mp.mpf(1)/2 - mp.mpf(p)/m)/m
        # Beta(p/m, 1/2-p/m) = G(p/m) G(1/2-p/m) / G(1/2),  G(1/2)=sqrt(pi)
        gprod = (mp.gamma(mp.mpf(p)/m)*mp.gamma(mp.mpf(1)/2 - mp.mpf(p)/m)/mp.sqrt(mp.pi))/m
        key = tuple(sorted([p, m//2 - p]))
        if key in seen:
            continue
        seen.add(key)
        args = [mp.mpf(p)/m, mp.mpf(1)/2 - mp.mpf(p)/m]
        print(f"      p={p}: B({p}/{m},{m//2-p}/{m}) = G({p}/{m})G({m//2-p}/{m})/sqrt(pi) / {m}"
              f"   [{mp.nstr(beta,25)}]  diff={mp.nstr(abs(beta-gprod),5)}")

print()
print("   Gamma.lean reaches G(k/24), k in Z, i.e. arguments 1/24, 2/24,..., 24/24 (mod ints).")
print("   -> denominators 1,2,3,4,6,8,12,24.")
for name, arg in [("m=6", mp.mpf(1)/6), ("m=6", mp.mpf(1)/3),
                  ("m=8", mp.mpf(1)/8), ("m=8", mp.mpf(3)/8), ("m=8", mp.mpf(1)/4),
                  ("m=10", mp.mpf(1)/10), ("m=10", mp.mpf(1)/5),
                  ("m=10", mp.mpf(3)/10), ("m=10", mp.mpf(2)/5)]:
    in24 = (arg*24) % 1
    newflag = "NEW" if abs(in24) > mp.mpf('1e-30') and abs(in24-1) > mp.mpf('1e-30') else "have"
    print(f"      {name}: G({mp.nstr(arg,6)}) = G({mp.nstr(arg*24,6)}/24)  -> {newflag}")

print()
print("== (C) the second-kind (arclength) integral diverges; no finite complete value ==")
for m in [6, 8, 10]:
    for U in [10, 100, 1000]:
        U = mp.mpf(U)
        g = mp.quad(lambda x: mp.sqrt(1+x**m), [0, 1, 2, 10, U])
        asym = (2/(m+2))*U**(mp.mpf(m)/2+1)
        print(f"   m={m} U={U}: int sqrt = {mp.nstr(g,22)}  (asympt (2/(m+2))U^(m/2+1) = {mp.nstr(asym,22)})")

print()
print("== (D) speed^2 degree / genus of the constructible closed curves ==")
# cubic Bezier with random P-constructible-ish control points
P = [(mp.mpf('0.3'), mp.mpf('0.7')), (mp.mpf('1.1'), mp.mpf('1.9')),
     (mp.mpf('2.2'), mp.mpf('-0.4')), (mp.mpf('0.5'), mp.mpf('1.3'))]
def bez(t):
    return (sum(mp.binomial(3, k)*(1-t)**(3-k)*t**k*P[k][0] for k in range(4)),
            sum(mp.binomial(3, k)*(1-t)**(3-k)*t**k*P[k][1] for k in range(4)))
def bez_d(t):
    # velocity components are quadratics
    return (3*sum(mp.binomial(2, k)*(1-t)**(2-k)*t**k*(P[k+1][0]-P[k][0]) for k in range(3)),
            3*sum(mp.binomial(2, k)*(1-t)**(2-k)*t**k*(P[k+1][1]-P[k][1]) for k in range(3)))
t = mp.mpf('0.37')
vx, vy = bez_d(t)
print(f"   cubic Bezier speed^2 at t=0.37: {mp.nstr(vx**2+vy**2,20)}")
print(f"   fit speed^2 = a t^4 + b t^3 + c t^2 + d t + e by 5 samples (quartic => exact):")
ts = [mp.mpf(k)/5 for k in range(5)]
vals = [(lambda v: v[0]**2+v[1]**2)(bez_d(s)) for s in ts]
import numpy as np
A = np.array([[float(s)**4, float(s)**3, float(s)**2, float(s), 1.0] for s in ts])
coef = np.linalg.solve(A, np.array([float(v) for v in vals]))
resid = max(abs((lambda v: v[0]**2+v[1]**2)(bez_d(s)) -
                sum(coef[k]*s**(4-k) for k in range(4)) - coef[4]) for s in [mp.mpf('0.1'), mp.mpf('0.63')])
print(f"   quartic coefficients = {coef}   max residual off 5 nodes = {mp.nstr(resid,5)}")
print("   -> speed^2 is a quartic, so int sqrt(speed^2) is a genus-1 (elliptic) integral.")
print("   poly_graph y = p(x), deg p = d <= 6:  speed^2 = 1 + p'(x)^2 has degree <= 2(d-1):")
for d in range(1, 7):
    print(f"      d={d}: deg speed^2 <= {2*(d-1)}  => genus = floor((deg-1)/2) = {(2*(d-1)-1)//2 if d >= 2 else 0}")

print()
print("== (F) incomplete arclength G(X) vs the closest Beta period (m=10) ==")
m = mp.mpf(10)
B_period = mp.beta(mp.mpf(1)/m, mp.mpf(1)/2 - mp.mpf(1)/m)/m
print(f"   Beta period (1/10)B(1/10,2/5) = {mp.nstr(B_period,30)}")
for X in ['0.5', '0.9', '1.0', '1.2', '2.0']:
    X = mp.mpf(X)
    G = mp.quad(lambda x: mp.sqrt(1+x**m), [0, X])
    print(f"   G({mp.nstr(X,4)}) = {mp.nstr(G,25)}   diff={mp.nstr(abs(G-B_period),5)}")
