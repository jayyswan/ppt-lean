"""R2-04: algebraic degrees of the cubic and sextic reductions (H5).

For the cubic (RBBG) and sextic (Robinson/Shen) parametrizations

    z = beta(p),  k^2 = alpha(p),  prefactor = gamma(p)
    xi = xi(p),   x(p),            prefactor = (1-x+x^2)^(1/4)

we eliminate p symbolically (sympy resultants) and, specialising the signature
argument z to a rational, factor the resulting univariate polynomials over Q to
get the TRUE minimal degrees of

    k^2, k^2 + 1/k^2,  prefactor^4,  prefactor^2,  prefactor
    x,   x(1-x),       (1-x+x^2),    prefactor

as algebraic functions of the signature argument (degree over Q(z) = degree of
the rational specialisation, as long as it stays irreducible).

Run: py R2-04-degrees.py
"""
import sympy as sp

p, A, B, GG, CC, XX, XI, P2 = sp.symbols('p A B GG CC XX XI P2')


def show(name, poly, var, spec, val):
    f = sp.factor(poly.subs(spec, val))
    if f == 0:
        print(f"  {name}: trivially 0 at {spec}={val}")
        return
    fl = sp.factor_list(f, var)
    degs = []
    for fac, mult in fl[1]:
        if fac.has(var):
            degs.append((sp.degree(fac, var), mult))
    print(f"  {name} at {spec}={val}: factors (degree,mult) = {degs}"
          f"  -> min degree {max(d for d, _ in degs)}")


def main():
    # ---------------- CUBIC ----------------
    gb = 4 * B * (1 + p + p ** 2) ** 3 - 27 * p ** 2 * (1 + p) ** 2
    fA = A * (1 + 2 * p) - p ** 3 * (2 + p)              # A = k^2
    fC = CC ** 2 * (1 + 2 * p) - (1 + p + p ** 2) ** 2   # CC = gamma
    fG = GG * (1 + 2 * p) - (1 + p + p ** 2) ** 2        # GG = gamma^2

    RA = sp.resultant(fA, gb, p)
    RG = sp.resultant(fG, gb, p)
    RC = sp.resultant(fC, gb, p)
    print("CUBIC  (z = beta(p), k^2 = alpha(p), gamma = (1+p+p^2)/sqrt(1+2p))")
    print("  relation R(k^2,z): degree in k^2 =", sp.degree(RA, A),
          ", in z =", sp.degree(RA, B))
    print("  gamma^2-relation : degree in gamma^2 =", sp.degree(RG, GG))
    print("  gamma-relation   : degree in gamma =", sp.degree(RC, CC))
    for val in [sp.Rational(3, 10), sp.Rational(1, 2), sp.Rational(1, 5)]:
        print(f"  --- z = {val} ---")
        show("k^2", RA, A, B, val)
        show("gamma^2", RG, GG, B, val)
        show("gamma", RC, CC, B, val)

    # ---------------- SEXTIC ----------------
    gx = 4 * XI * (1 + p + p ** 2) ** 3 - 27 * p ** 2 * (1 + p) ** 2
    fx = XX * (1 + 2 * p) - p * (2 + p)                  # XX = x = k^2
    fp = P2 * (1 + 2 * p) - (1 + p + p ** 2)             # P2 = prefactor^2

    RX = sp.resultant(fx, gx, p)
    RP = sp.resultant(fp, gx, p)
    print("\nSEXTIC (z = xi(p), x = p(2+p)/(1+2p), pref = (1-x+x^2)^(1/4))")
    print("  relation R(x,z): degree in x =", sp.degree(RX, XX),
          ", in z =", sp.degree(RX, XI))
    print("  prefactor^2-relation: degree in pref^2 =", sp.degree(RP, P2))
    for val in [sp.Rational(3, 10), sp.Rational(1, 2), sp.Rational(1, 5)]:
        print(f"  --- z = {val} ---")
        show("x", RX, XX, XI, val)
        show("pref^2", RP, P2, XI, val)

    # y = x(1-x) cubic, and clean sextic relation
    print("\nSEXTIC clean checks:")
    print("  16 z(1-z)(1-x+x^2)^3 - 27 x^2(1-x)^2 factors:",
          sp.factor(16 * XI * (1 - XI) * (1 - XX + XX ** 2) ** 3 - 27 * XX ** 2 * (1 - XX) ** 2))
    print("  (1-x+x^2) = (1+p+p^2)^2/(1+2p)^2 :",
          sp.simplify((1 - p * (2 + p) / (1 + 2 * p) + (p * (2 + p) / (1 + 2 * p)) ** 2)
                      - (1 + p + p ** 2) ** 2 / (1 + 2 * p) ** 2))


if __name__ == "__main__":
    main()
