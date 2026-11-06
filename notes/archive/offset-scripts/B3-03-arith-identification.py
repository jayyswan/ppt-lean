# B3-03-arith-identification.py
# Q6: irreducibility / factorization / mod-p cycle types of the foot polynomials,
# and PSLQ-type identification of the numbers.  mpmath 40 dps.
import sympy as sp
import mpmath as mp

mp.mp.dps = 40
x = sp.symbols('x')

def section(t):
    print("\n" + "=" * 70)
    print(t)
    print("=" * 70)

def modp_factor_degrees(poly, primes):
    print("  mod-p factorization degree patterns:")
    for q in primes:
        fac = sp.factor_list(poly, modulus=q)[1]
        degs = sorted([sp.degree(f, x) for f, m in fac for _ in range(m)])
        print(f"    p={q}: {degs}")

section("foot polynomial for min-dist from (0,1) to y=x^7")
P = 7*x**12 - 7*x**5 + 1
print("P =", P)
print("is_irreducible over Q:", sp.Poly(P, x).is_irreducible)
print("factor over Q:", sp.factor(P))
modp_factor_degrees(P, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])
print("discriminant squarefree part:",
      sp.factor(sp.discriminant(sp.Poly(P, x))))

section("foot polynomial for min-dist from (1,0) to y=x^7")
P2 = 7*x**13 + x - 1
print("is_irreducible over Q:", sp.Poly(P2, x).is_irreducible)
modp_factor_degrees(P2, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31])

section("check parity / special structure of 7x^12-7x^5+1")
print("P(-x) =", sp.expand(P.subs(x, -x)))
print("substitute x^5 = u / x^12 = ? :", sp.factor(P))
# lattice/Cohn-like: does it factor over Q(sqrt(5))?
for s in [2, 3, 5, -1, -2, -3]:
    f = sp.factor(P, extension=sp.sqrt(s))
    if f != sp.factor(P):
        print(f"  factors over Q(sqrt({s})): {f}")

section("numeric identification of min-dist values")
vals = {
 "t_(0,1)_root1": mp.mpf('0.687951574050468880810466029919'),
 "t_(0,1)_root2": mp.mpf('0.975052597739749303492561805282'),
 "dist_(0,1)": mp.sqrt(mp.mpf('0.687951574050468880810466029919')**2
                       + (mp.mpf('0.687951574050468880810466029919')**7-1)**2),
 "dist_(0,1)_alt": mp.sqrt(mp.mpf('0.975052597739749303492561805282')**2
                       + (mp.mpf('0.975052597739749303492561805282')**7-1)**2),
 "t_(1,0)": mp.mpf('0.769159571193067978732271085199'),
 "dist_(1,0)": mp.sqrt(mp.mpf('0.769159571193067978732271085199')**2
                       + mp.mpf('0.769159571193067978732271085199')**14),
}
for k, v in vals.items():
    print(f"  {k} = {mp.nstr(v, 30)}")
    print(f"      identify(v) = {mp.identify(v)}")
    if k.startswith("dist"):
        for basis in [([1, mp.pi, mp.log(2), mp.euler], '1,pi,log2,euler'),
                      ([1, mp.pi, mp.log(2), mp.log(3)], '1,pi,log2,log3')]:
            pass
# PSLQ: is dist_(0,1) a low-degree algebraic number? (test degree<=12 minimal poly)
for name in ["dist_(0,1)", "dist_(1,0)"]:
    v = vals[name]
    print(f"  {name}: minimal-polynomial search (mpmath.pslq ints)")
    poly = mp.pslq([v**k for k in range(0, 7)], maxcoeff=10**40, maxsteps=10**6)
    print("    pslq deg<=6:", poly)
