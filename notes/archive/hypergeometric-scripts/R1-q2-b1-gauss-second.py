"""R1-Q2: B1 frontier -- for which a is 2F1(a,1-a;1;1/2) reachable?

Gauss's second theorem (Gauss 1812; DLMF 15.4.26):
    2F1(a, 1-a; 1; 1/2) = sqrt(pi) / ( Gamma((1+a)/2) Gamma(1 - a/2) ).
Reaching the left side makes the right side (a Gamma product) P-constructible.

Checks:
 (1) Gauss second, >= 30 digits, for the four "reachable" a and for new a.  [NC]
 (2) The four reachable signatures, by algebraic reduction to K:
       a = 1/2 : V6 quadratic  2F1(1/2,1/2;1;z) = 2F1(1/4,1/4;1;4z(1-z))
       a = 1/4 : V7 quartic    2F1(1/4,3/4;1;z) = (1+sqrt z)^(-1/2) 2F1(1/2,1/2;1;2 sqrt z/(1+sqrt z))
       a = 1/3 : cubic  (verified only through the Gauss-second value; R2 owns the reduction)
       a = 1/6 : sextic (same)
 (3) Bailey's z=1/2 formula  2F1(a,1-a;c;1/2) = G(c/2)G((c+1)/2)/(G((c+a)/2)G((c+1-a)/2))
     -- tested, to know whether other c help.                                [NC / REFUTED?]
 (4) The H6-transformed family 2F1(-1/2,1;c;1/2) (what the Euler transform of the
     power-law value at z=-1 gives) is NOT a Gamma product.                    [NC]
 (5) PSLQ-style identification of the a=1/3 and a=1/6 Gauss-second values.
"""
import mpmath as mp

mp.mp.dps = 50


def dg(x):
    return -mp.log10(abs(x)) if x > 0 else mp.inf


print("== (1) Gauss's second theorem: 2F1(a,1-a;1;1/2) vs sqrt(pi)/(G((1+a)/2)G(1-a/2)) ==")
print(f"{'a':>10} {'2F1':>26} {'|diff|':>12} {'digits':>8}")
allA = [mp.mpf(1)/2, mp.mpf(1)/3, mp.mpf(1)/4, mp.mpf(1)/6, mp.mpf(1)/5,
        mp.mpf(1)/8, mp.mpf(3)/10, mp.mpf(2)/5, mp.mpf(3)/7, mp.mpf(3)/8,
        mp.mpf('0.37'), mp.mpf('0.123')]
for a in allA:
    L = mp.hyp2f1(a, 1-a, 1, mp.mpf(1)/2)
    R = mp.sqrt(mp.pi)/(mp.gamma((1+a)/2)*mp.gamma(1-a/2))
    d = abs(L-R)
    print(f"{mp.nstr(a,10):>10} {mp.nstr(L,26):>26} {mp.nstr(d,5):>12} {mp.nstr(dg(d),5):>8}")

print()
print("== (2a) a=1/2: V6 quadratic at z=1/2 (== Gauss second), and K form ==")
z = mp.mpf(1)/2
lhs = mp.hyp2f1(mp.mpf(1)/2, mp.mpf(1)/2, 1, z)
rhs = mp.hyp2f1(mp.mpf(1)/4, mp.mpf(1)/4, 1, 4*z*(1-z))
K = mp.ellipk(mp.mpf(1)/2)          # mpmath uses parameter m=k^2
print(f"   2F1(1/2,1/2;1;1/2) = {mp.nstr(lhs,30)}")
print(f"   2F1(1/4,1/4;1;4z(1-z))= {mp.nstr(rhs,30)}  diff={mp.nstr(abs(lhs-rhs),5)}")
print(f"   (2/pi)K(1/2)          = {mp.nstr(2/mp.pi*K,30)}  diff={mp.nstr(abs(lhs-2/mp.pi*K),5)}")
print(f"   sqrt(pi)/G(3/4)^2     = {mp.nstr(mp.sqrt(mp.pi)/mp.gamma(mp.mpf(3)/4)**2,30)}")

print()
print("== (2b) a=1/4: V7 quartic at z=1/5 ==")
z = mp.mpf(1)/5
lhs = mp.hyp2f1(mp.mpf(1)/4, mp.mpf(3)/4, 1, z)
s = mp.sqrt(z); w = 2*s/(1+s)
rhs = (1+s)**(mp.mpf(-1)/2)*mp.hyp2f1(mp.mpf(1)/2, mp.mpf(1)/2, 1, w)
print(f"   z=1/5  w={mp.nstr(w,25)}")
print(f"   LHS = {mp.nstr(lhs,30)}  RHS = {mp.nstr(rhs,30)}  diff={mp.nstr(abs(lhs-rhs),5)}")
print(f"   Gauss2 for a=1/4: {mp.nstr(mp.sqrt(mp.pi)/(mp.gamma(mp.mpf(5)/8)*mp.gamma(mp.mpf(7)/8)),30)}")

print()
print("== (2c) a=1/3 and a=1/6: Gauss-second values (reductions owned by R2) ==")
for a in [mp.mpf(1)/3, mp.mpf(1)/6]:
    L = mp.hyp2f1(a, 1-a, 1, mp.mpf(1)/2)
    R = mp.sqrt(mp.pi)/(mp.gamma((1+a)/2)*mp.gamma(1-a/2))
    print(f"   a={mp.nstr(a,4)}: LHS={mp.nstr(L,35)}")
    print(f"            RHS={mp.nstr(R,35)}  diff={mp.nstr(abs(L-R),5)}")

print()
print("== (3) Bailey z=1/2 formula for 2F1(a,1-a;c;1/2): test candidates ==")
def bailey(a, c):
    return (mp.gamma(c/2)*mp.gamma((c+1)/2) /
            (mp.gamma((c+a)/2)*mp.gamma((c+1-a)/2)))
for (a, c) in [(mp.mpf(1)/2, 1), (mp.mpf(1)/2, 2), (mp.mpf(1)/3, mp.mpf(3)/2),
               (mp.mpf(2)/5, mp.mpf('1.7')), (mp.mpf('0.37'), mp.mpf('0.9'))]:
    L = mp.hyp2f1(a, 1-a, c, mp.mpf(1)/2)
    R = bailey(a, c)
    print(f"   a={mp.nstr(a,4):>5} c={mp.nstr(c,4):>5}: 2F1={mp.nstr(L,25)}"
          f" bailey={mp.nstr(R,25)} diff={mp.nstr(abs(L-R),5)}")

print()
print("== (4) Euler transform of the power-law value at z=-1: sqrt2*2F1(-1/2,1;c;1/2) ==")
for m in [6, 8, 10]:
    c = 1 + mp.mpf(1)/m
    val = mp.hyp2f1(mp.mpf(-1)/2, 1/m, c, mp.mpf(-1))
    eul = mp.sqrt(2)*mp.hyp2f1(mp.mpf(-1)/2, 1, c, mp.mpf(1)/2)
    print(f"   m={m}: 2F1(-1/2,1/m;1+1/m;-1)={mp.nstr(val,28)}"
          f"  sqrt2*2F1(-1/2,1;c;1/2) diff={mp.nstr(abs(val-eul),5)}")

print()
print("== (5) closed forms of the new-signature values (PSLQ over {1,pi,G1/3,G1/3^2,G1/3^3}) ==")
G13 = mp.gamma(mp.mpf(1)/3)
pi = mp.pi
for name, val in [("a=1/3", mp.hyp2f1(mp.mpf(1)/3, mp.mpf(2)/3, 1, mp.mpf(1)/2)),
                  ("a=1/6", mp.hyp2f1(mp.mpf(1)/6, mp.mpf(5)/6, 1, mp.mpf(1)/2))]:
    basis = [mp.mpf(1), pi, G13, G13**2, G13**3, pi*G13, pi*G13**2, pi*G13**3]
    rel = mp.pslq([val]+basis, maxcoeff=10**8, maxsteps=10**6)
    print(f"   {name}: value={mp.nstr(val,30)}  PSLQ relation coeffs={rel}")
    if rel:
        # solve for val
        coeffs = rel[1:]
        rhs = -sum(c*b for c, b in zip(coeffs, basis))
        print(f"           => value = {mp.nstr(rhs/rel[0],30)}"
              f"  residual={mp.nstr(abs(val-rhs/rel[0]),5)}")
    # compare with the classical singular-value expression
print("   classical: K(k3)=3^(1/4) G(1/3)^3/(2^(7/3) pi), k3=(sqrt3-1)/(2 sqrt2), and")
print("             K(k6)^2 relates to G(1/24)G(5/24)G(7/24)G(11/24)/...")
k3 = (mp.sqrt(3)-1)/(2*mp.sqrt(2))
K3 = mp.ellipk(k3**2)
print(f"   K(k3) = {mp.nstr(K3,30)}")
print(f"   3^(1/4)G(1/3)^3/(2^(7/3)pi) = {mp.nstr(3**mp.mpf('0.25')*G13**3/(2**mp.mpf(7)/3**0*mp.pi),30)}")

print()
print("== (6) Bailey z=1/2 formula over a grid (guards against coincidence) ==")
worst = mp.mpf(0); worst_pt = None
import random
random.seed(12345)
pts = [(mp.mpf(1)/d, mp.mpf(1)/e) for d in range(2, 13) for e in range(1, 13)]
pts += [(mp.mpf(random.random()), mp.mpf('0.2')+mp.mpf(random.random())) for _ in range(40)]
for (a, c) in pts:
    try:
        L = mp.hyp2f1(a, 1-a, c, mp.mpf(1)/2)
        R = bailey(a, c)
        d = abs(L-R)
        if d > worst:
            worst, worst_pt = d, (a, c)
    except Exception:
        pass
print(f"   {len(pts)} (a,c) pairs; worst |2F1 - Bailey| = {mp.nstr(worst,5)}"
      f" at (a,c)={worst_pt}  digits={mp.nstr(dg(worst),5)}")

print()
print("== (7) Euler transform (a,b;c;z) = (1-z)^(-a) (a,c-b;c;z/(z-1)), interior check ==")
for (a, b, c, z) in [(mp.mpf(-1)/2, mp.mpf(1)/6, mp.mpf(7)/6, mp.mpf(-1)/2),
                     (mp.mpf(1)/3, mp.mpf(2)/5, mp.mpf(9)/10, mp.mpf('0.3')),
                     (mp.mpf(1)/4, mp.mpf(3)/4, mp.mpf(1), mp.mpf('-0.4'))]:
    L = mp.hyp2f1(a, b, c, z)
    w = z/(z-1)
    R = (1-z)**(-a)*mp.hyp2f1(a, c-b, c, w)
    print(f"   a={mp.nstr(a,4)} b={mp.nstr(b,4)} c={mp.nstr(c,4)} z={mp.nstr(z,4)}:"
          f" diff={mp.nstr(abs(L-R),5)}")
