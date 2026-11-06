"""R1-Q4 (bonus): can the EXISTING elliptic primitive reach Gamma(1/5)?

ellipticF_Pconstructible gives K(k) = (pi/2) 2F1(1/2,1/2;1;k^2) for every
P-constructible modulus k < 1.  The Chowla-Selberg formula expresses the period
of the CM elliptic curve of discriminant -D as an algebraic multiple of a product
of Gamma(k/D).  If a singular modulus (algebraic, hence P-constructible) has
K = algebraic * Gamma-product, that Gamma product becomes P-constructible.

K is computed from the nome:  K(tau) = (pi/2) theta_3(0,q)^2,  q = exp(i pi tau).

Method validation on d=-4 (ratio is exactly 1), then the decisive small-coefficient
minimal-polynomial test for tau = i sqrt5 (discriminant -20, denominator 5).
"""
import mpmath as mp

mp.mp.dps = 60


def K_of_tau(tau):
    q = mp.e ** (1j * mp.pi * tau)
    return (mp.pi/2 * mp.jtheta(3, 0, q)**2)


def k_of_tau(tau):
    q = mp.e ** (1j * mp.pi * tau)
    return (mp.jtheta(2, 0, q)/mp.jtheta(3, 0, q))**2      # k^2 = lambda


def minpoly_small(r, maxcoeff=10**6, maxdeg=6):
    for deg in range(1, maxdeg+1):
        rel = mp.pslq([r**k for k in range(deg+1)], maxcoeff=maxcoeff, maxsteps=10**6)
        if rel:
            return deg, rel
    return None, None


print("== validation: d=-4 (tau=i), expected K = G(1/4)^2/(4 sqrt(pi)) ==")
K4 = K_of_tau(mp.mpc(0, 1))
print("   K(i) =", mp.nstr(K4, 40))
print("   residual =", mp.nstr(K4 - mp.gamma(mp.mpf(1)/4)**2/(4*mp.sqrt(mp.pi)), 5))
r4 = K4*4*mp.sqrt(mp.pi)/mp.gamma(mp.mpf(1)/4)**2
print("   K*4 sqrt(pi)/G(1/4)^2 =", mp.nstr(r4, 30), " -> minpoly:", minpoly_small(r4))

print()
print("== d=-3: K(k3), k3=(sqrt3-1)/(2 sqrt2), known = 3^(1/4)G(1/3)^3/(2^(7/3)pi) ==")
k3 = (mp.sqrt(3)-1)/(2*mp.sqrt(2))
K3 = mp.ellipk(k3**2)
G13 = mp.gamma(mp.mpf(1)/3)
known3 = 3**mp.mpf('0.25')*G13**3/(2**(mp.mpf(7)/3)*mp.pi)      # 3^(1/4) G(1/3)^3 / (2^(7/3) pi)
print("   K(k3)  =", mp.nstr(K3, 35))
print("   formula=", mp.nstr(known3, 35), " residual=", mp.nstr(K3-known3, 5))

print()
print("== d=-20 (tau=i sqrt5): is K an algebraic multiple of a Gamma(k/5)-product? ==")
K = K_of_tau(mp.mpc(0, mp.sqrt(5)))
K = K.real
print("   K(i sqrt5) =", mp.nstr(K, 40))
G = {k: mp.gamma(mp.mpf(k)/5) for k in [1, 2, 3, 4]}
cands = {
    "G(1/5)G(2/5)/pi":   G[1]*G[2]/mp.pi,
    "G(1/5)G(2/5)/pi^2": G[1]*G[2]/mp.pi**2,
    "G(1/5)^2/pi":       G[1]**2/mp.pi,
    "G(2/5)^2/pi":       G[2]**2/mp.pi,
    "G(1/5)G(2/5)":      G[1]*G[2],
    "G(1/5)G(2/5)/sqrt(pi)": G[1]*G[2]/mp.sqrt(mp.pi),
}
for name, val in cands.items():
    r = K/val
    deg, rel = minpoly_small(r)
    flag = "ALGEBRAIC" if deg else "not algebraic (<= deg 6, coeff 1e6)"
    print(f"   K/({name}) = {mp.nstr(r,25)}  -> {flag}  {rel}")

print()
print("== d=-20 richer basis: products of G(k/20), k odd ==")
ks = [1, 3, 7, 9, 11, 13, 17, 19]
P = mp.fprod([mp.gamma(mp.mpf(k)/20) for k in ks])
print("   P = prod G(k/20) =", mp.nstr(P, 35))
for name, val in [("P", P), ("P/pi^4", P/mp.pi**4), ("P/pi^2", P/mp.pi**2),
                  ("sqrt(P)", mp.sqrt(P))]:
    r = K/val
    deg, rel = minpoly_small(r)
    flag = "ALGEBRAIC" if deg else "not algebraic (<= deg 6, coeff 1e6)"
    print(f"   K/({name}) = {mp.nstr(r,25)}  -> {flag}  {rel}")

print()
print("== note: tau=(-1+i sqrt5)/2 gives a complex K in the nome normalisation")
print("   (a different isogenous model); the real period would need an extra")
print("   algebraic conversion, so it is not used for the decisive test.")
