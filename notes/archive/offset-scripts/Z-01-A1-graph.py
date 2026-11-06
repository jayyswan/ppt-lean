# Z-01: independent re-verification of A1 ("degree 4n-2 from a polynomial graph offset").
# Re-derives from scratch: P(t)=p(t)^2(1+p'(t)^2)-d^2, genuine-crossing sign, X=t+p p',
# minimal polynomial of X, irreducibility, real-root pattern, Galois cycle types mod primes.
# Claimed: n=4 -> P deg 14, X deg 14; n=5 -> 18; n=6 -> 22.
import sympy as sp

t, X = sp.symbols('t X', real=True)


def galois_cycle_types(poly, primes=(1000003, 2000003, 3000017, 4000037, 5000011)):
    out = []
    for q in primes:
        try:
            fac = sp.factor_list(poly, modulus=q)[1]
            degs = sorted([f[0].degree() for f in fac for _ in range(f[1])])
            mults = sorted([(f[0].degree(), f[1]) for f in fac])
            out.append((q, degs, mults))
        except Exception as e:  # pragma: no cover
            out.append((q, 'ERR ' + str(e), None))
    return out


def analyse(n, coeffs_eventually):
    # p(t) = t^n + t + 1
    p = t ** n + t + 1
    pp = sp.diff(p, t)
    P = sp.expand(p ** 2 * (1 + pp ** 2) - 1)   # d = -1
    Ppoly = sp.Poly(P, t)
    print(f"--- n={n}: p = {p} (d=-1)")
    print(f"    deg P = {Ppoly.degree()}  (expected {4*n-2})")
    print(f"    irreducible over Q: {sp.Poly(P, t).is_irreducible}")

    # genuine crossings: roots of P with p*sqrt(1+p'^2) = -d = 1
    real_roots = sp.real_roots(Ppoly)
    print(f"    real roots of P (exact surds if any): {len(real_roots)}")
    rn = sp.nroots(Ppoly, n=50, maxsteps=200)
    realapprox = sorted([complex(r).real for r in rn if abs(complex(r).imag) < sp.Float('1e-40')])
    print(f"    real roots (~50d): {[sp.N(r, 40) for r in realapprox]}")
    for r in realapprox:
        val = complex(sp.N(p.subs(t, r) * sp.sqrt(1 + pp.subs(t, r) ** 2) - 1, 60))
        print(f"      t={sp.N(r,40)}: p*sqrt(1+p'^2)-1 = {val:.3e}")

    # X = t + p p'; minimal polynomial via resultant over Q
    Xexpr = sp.expand(t + p * pp)
    res = sp.resultant(Ppoly, X - Xexpr, t)
    resp = sp.Poly(sp.expand(res), X)
    # strip content
    cont = sp.gcd(resp.all_coeffs())
    resp = sp.Poly([sp.Rational(c, cont) for c in resp.all_coeffs()], X)
    print(f"    minimal-poly candidate deg = {resp.degree()}, irreducible: {resp.is_irreducible}")
    lc = resp.LC()
    print(f"    monic form: {sp.Poly([sp.nsimplify(c/lc) for c in resp.all_coeffs()], X).as_expr()}")
    # print integer primitive form scaled so leading coeff nice
    prim = sp.Poly(sp.expand(res), X).primitive()[1]
    print(f"    primitive integer poly (scaled): {prim.as_expr()}")
    return Ppoly, prim, realapprox


for n in (4, 5, 6):
    Ppoly, prim, reals = analyse(n, None)

print()
print("=== Galois cycle types for the n=4 degree-14 X-polynomial ===")
p4 = t ** 4 + t + 1
pp4 = sp.diff(p4, t)
P4 = sp.expand(p4 ** 2 * (1 + pp4 ** 2) - 1)
Xe4 = sp.expand(t + p4 * pp4)
res4 = sp.Poly(sp.expand(sp.resultant(sp.Poly(P4, t), X - Xe4, t)), X).primitive()[1]
for q, degs, mults in galois_cycle_types(res4):
    print(f"    mod {q}: degree multiset {mults} -> factors {degs}")
