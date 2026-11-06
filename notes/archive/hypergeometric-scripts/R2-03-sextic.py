"""R2-03: SEXTIC reduction of the signature-6 integral (H5).

Identity (Shen, Ramanujan J. 30 (2013); P.L. Robinson, arXiv:2009.07069, Thm 8):

    2F1(1/6, 5/6; 1; xi)  =  (1 - x + x^2)^(1/4) * 2F1(1/2, 1/2; 1; x)

where the increasing bijection x -> xi of (0,1) onto (0,1) is given by

    4 xi (1 - xi) = (27/4) x^2 (1-x)^2 / (1 - x + x^2)^3.

Equivalent parametric form (p in (0,1)):

    x(p)  = p (2+p) / (1+2p),
    xi(p) = (27/4) p^2 (1+p)^2 / (1+p+p^2)^3,
    prefactor = (1-x+x^2)^(1/4) = sqrt(1+p+p^2) / sqrt(1+2p).

Note the clean forms
    1 - x + x^2 = (1+p+p^2)^2 / (1+2p)^2,
and, with y := x(1-x), the relation is the CUBIC
    27 y^2 = 16 xi (1-xi) (1-y)^3.

Domain: p in (0,1) ==> x, xi in (0,1).  For p in (-1/2,0) one gets x, xi
with x in (-1,0); the identity still holds there (both series converge).
Run: py R2-03-sextic.py
"""
import mpmath as mp

mp.mp.dps = 80


def F16(z):
    return mp.hyp2f1(mp.mpf(1) / 6, mp.mpf(5) / 6, 1, z)


def F12(z):
    return mp.hyp2f1(mp.mpf(1) / 2, mp.mpf(1) / 2, 1, z)


def x_of(p):
    return p * (2 + p) / (1 + 2 * p)


def xi_of(p):
    return (27 * p ** 2 * (1 + p) ** 2) / (4 * (1 + p + p ** 2) ** 3)


def pref(p):
    return mp.sqrt((1 + p + p ** 2) / (1 + 2 * p))


def digits(diff):
    return mp.inf if diff == 0 else -mp.log10(abs(diff))


def main():
    ps = [mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(1) / 2, mp.mpf(2) / 3,
          mp.mpf(3) / 4, mp.mpf(9) / 10, -mp.mpf(1) / 4]
    print("(A) identity:  2F1(1/6,5/6;1;xi(p)) = pref(p) 2F1(1/2,1/2;1;x(p))")
    print(f"{'p':>10} {'x=k2':>22} {'xi=z':>22} {'pref':>22} {'|lhs-rhs|':>12} {'dig':>7}")
    worst = mp.mpf(0)
    for p in ps:
        x, xi, P = x_of(p), xi_of(p), pref(p)
        diff = abs(F16(xi) - P * F12(x))
        worst = max(worst, diff)
        print(f"{mp.nstr(p,6):>10} {mp.nstr(x,20):>22} {mp.nstr(xi,20):>22} "
              f"{mp.nstr(P,20):>22} {mp.nstr(diff,5):>12} {mp.nstr(digits(diff),6):>7}")
    print("  worst |lhs-rhs| =", mp.nstr(worst, 5), " digits =", mp.nstr(digits(worst), 6))

    print("\n(B) V7-shape: solve xi(p)=z for p in (0,1), then x=x(p):")
    for z in [mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(1) / 2, mp.mpf(3) / 4, mp.mpf(9) / 10]:
        p = mp.findroot(lambda x: xi_of(x) - z, (mp.mpf('0.01'), mp.mpf('0.9999')))
        x, P = x_of(p), pref(p)
        diff = abs(F16(z) - P * F12(x))
        print(f"  z={mp.nstr(z,6):>8}  p={mp.nstr(p,18):>20}  x={mp.nstr(x,18):>20} "
              f" err={mp.nstr(diff,4):>10}  dig={mp.nstr(digits(diff),5)}")

    print("\n(C) auxiliary relations:")
    for p in ps:
        x, xi = x_of(p), xi_of(p)
        y = x * (1 - x)
        rel = 16 * xi * (1 - xi) * (1 - x + x ** 2) ** 3 - 27 * x ** 2 * (1 - x) ** 2
        cub = 27 * y ** 2 - 16 * xi * (1 - xi) * (1 - y) ** 3
        # check 4 xi (1-xi) = (27/4) x^2(1-x)^2/(1-x+x^2)^3
        rel2 = 4 * xi * (1 - xi) - (mp.mpf(27) / 4) * x ** 2 * (1 - x) ** 2 / (1 - x + x ** 2) ** 3
        print(f"  p={mp.nstr(p,6):>8}  sexticrel={mp.nstr(rel,4):>10}  "
              f"4xi(1-xi)-form={mp.nstr(rel2,4):>10}  cubic(y)={mp.nstr(cub,4):>10}")

    print("\n(D) endpoints: xi(0)=0=x(0); xi(1)=1=x(1); pref(1)=1")

    print("\n(E) exact special value at xi=1/2 (p=(sqrt3-1)/2, x=1/2, pref=(3/4)^(1/4)):")
    lhs = F16(mp.mpf(1) / 2)
    rhs = (mp.mpf(3) / 4) ** (mp.mpf(1) / 4) * F12(mp.mpf(1) / 2)
    print("  2F1(1/6,5/6;1;1/2) =", mp.nstr(lhs, 30))
    print("  (3/4)^(1/4)*2F1(1/2,1/2;1;1/2) =", mp.nstr(rhs, 30))
    print("  diff =", mp.nstr(abs(lhs - rhs), 5), " dig =", mp.nstr(digits(lhs - rhs), 6))

    print("\n(F) negative branch: convergence of RHS needs |x|<1, i.e. p in (-2+sqrt3, 0):")
    pn = -2 + mp.sqrt(3)
    print("  p=-2+sqrt3:", mp.nstr(pn, 20), " x(p)=", mp.nstr(x_of(pn), 20),
          " xi(p)=", mp.nstr(xi_of(pn), 20))


if __name__ == "__main__":
    main()
