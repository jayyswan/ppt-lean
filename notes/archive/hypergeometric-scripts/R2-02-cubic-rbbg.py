"""R2-02: Ramanujan / Berndt-Bhargava-Garvan CUBIC reduction (H5).

Identity (Berndt-Bhargava-Garvan 1995, Thm 5.6; Ramanujan's 2nd notebook p. 258):

    2F1(1/3, 2/3; 1; beta(p)) = gamma(p) * 2F1(1/2, 1/2; 1; alpha(p)),

    alpha(p) = p^3 (2+p) / (1+2p)                (argument of K = classical k^2)
    beta(p)  = 27 p^2 (1+p)^2 / (4 (1+p+p^2)^3)  (signature-3 argument z)
    gamma(p) = (1+p+p^2) / sqrt(1+2p)            (prefactor)

Standard real domain 0 <= p < 1  ==>  alpha, beta in [0,1).
Extended domain (Shpot arXiv:2411.19608): -1/2 < p < 1, with a Pfaff branch
when -1/2 < p < p* (p* = -(1+sqrt3-sqrt(2 sqrt3))/2 ~ -0.435).

Also checks the eliminated algebraic relation R_c(k^2, z) = 0, which is
palindromic of bidegree (6,4): the invariant t = k^2 + 1/k^2 obeys an
irreducible CUBIC (the "cubic modular equation").
Run: py R2-02-cubic-rbbg.py
"""
import mpmath as mp

mp.mp.dps = 80


def F13(z):
    return mp.hyp2f1(mp.mpf(1) / 3, mp.mpf(2) / 3, 1, z)


def F12(z):
    return mp.hyp2f1(mp.mpf(1) / 2, mp.mpf(1) / 2, 1, z)


def alpha(p):
    return p ** 3 * (2 + p) / (1 + 2 * p)


def beta(p):
    return 27 * p ** 2 * (1 + p) ** 2 / (4 * (1 + p + p ** 2) ** 3)


def gamma(p):
    return (1 + p + p ** 2) / mp.sqrt(1 + 2 * p)


# ---- eliminated cubic relation R_c(A,B)=0, A=k^2, B=z (from Wolfram resultants) ----
def Rc(A, B):
    c0 = 256 * (B - 1) * B ** 3
    c1 = -768 * (B - 1) * B ** 3
    c2 = 3 * (6561 - 17496 * B + 15552 * B ** 2 - 5120 * B ** 3 + 512 * B ** 4)
    c3 = -2 * (19683 - 52488 * B + 46656 * B ** 2 - 14720 * B ** 3 + 896 * B ** 4)
    return c0 * (A ** 6 + 1) + c1 * (A ** 5 + A) + c2 * (A ** 4 + A ** 2) + c3 * A ** 3


def Qcubic(t, B):
    """cubic satisfied by t = A + 1/A  (divide R_c by A^3)."""
    c0 = 256 * (B - 1) * B ** 3
    c1 = -768 * (B - 1) * B ** 3
    c2 = 3 * (6561 - 17496 * B + 15552 * B ** 2 - 5120 * B ** 3 + 512 * B ** 4)
    c3 = -2 * (19683 - 52488 * B + 46656 * B ** 2 - 14720 * B ** 3 + 896 * B ** 4)
    return c0 * t ** 3 + c1 * t ** 2 + (c2 - 3 * c0) * t + (c3 - 2 * c1)


def digits(diff):
    return mp.inf if diff == 0 else -mp.log10(abs(diff))


def main():
    ps = [mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(1) / 2, mp.mpf(2) / 3,
          mp.mpf(3) / 4, mp.mpf(9) / 10]
    print("(A) parametric RBBG:  2F1(1/3,2/3;1;beta(p)) = gamma(p) 2F1(1/2,1/2;1;alpha(p))")
    print(f"{'p':>10} {'z=beta':>22} {'k2=alpha':>22} {'gamma':>22} {'|lhs-rhs|':>12} {'dig':>7}")
    worst = mp.mpf(0)
    for p in ps:
        z, k2, g = beta(p), alpha(p), gamma(p)
        diff = abs(F13(z) - g * F12(k2))
        worst = max(worst, diff)
        print(f"{mp.nstr(p,6):>10} {mp.nstr(z,20):>22} {mp.nstr(k2,20):>22} "
              f"{mp.nstr(g,20):>22} {mp.nstr(diff,5):>12} {mp.nstr(digits(diff),6):>7}")
    print("  worst |lhs-rhs| =", mp.nstr(worst, 5), " digits =", mp.nstr(digits(worst), 6))

    print("\n(B) V7-shape: solve beta(p)=z for p, then k2=alpha(p):")
    for z in [mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(1) / 2, mp.mpf(3) / 4, mp.mpf(17) / 20]:
        # beta is increasing on (0,1): bracket and bisect
        p = mp.findroot(lambda x: beta(x) - z, (mp.mpf('0.05'), mp.mpf('0.9999')))
        k2, g = alpha(p), gamma(p)
        diff = abs(F13(z) - g * F12(k2))
        print(f"  z={mp.nstr(z,6):>8}  p={mp.nstr(p,18):>20}  k2={mp.nstr(k2,18):>20} "
              f" err={mp.nstr(diff,4):>10}  dig={mp.nstr(digits(diff),5)}")

    print("\n(C) eliminated relation and invariant cubic:")
    for p in ps:
        z, k2 = beta(p), alpha(p)
        t = k2 + 1 / k2
        r = Rc(k2, z)
        q = Qcubic(t, z)
        print(f"  p={mp.nstr(p,6):>8}  R_c(k2,z)={mp.nstr(r,4):>12}   Q_c(k2+1/k2,z)={mp.nstr(q,4):>12}")

    print("\n(D) endpoints / domain:")
    print("  beta(0)=0, beta(1)=1; alpha(0)=0, alpha(1)=1; gamma(1)=sqrt(3)="
          + mp.nstr(mp.sqrt(3), 20))
    print("  p* (alpha=-1) =", mp.nstr(-(1 + mp.sqrt(3) - mp.sqrt(2 * mp.sqrt(3))) / 2, 20))

    print("\n(E) exact special value at z=1/2 (p=(sqrt3-1)/2, k2=(2-sqrt3)/4, gamma=3^(3/4)/2):")
    p = (mp.sqrt(3) - 1) / 2
    k2 = (2 - mp.sqrt(3)) / 4
    g = 3 ** (mp.mpf(3) / 4) / 2
    lhs = F13(mp.mpf(1) / 2)
    rhs = g * F12(k2)
    print("  2F1(1/3,2/3;1;1/2) = ", mp.nstr(lhs, 30))
    print("  (3^(3/4)/2)*2F1(1/2,1/2;1;(2-sqrt3)/4) =", mp.nstr(rhs, 30))
    print("  diff =", mp.nstr(abs(lhs - rhs), 5), " dig =", mp.nstr(digits(lhs - rhs), 6))
    print("  check gamma from p:", mp.nstr(gamma(p), 25), " 3^(3/4)/2:", mp.nstr(g, 25))
    print("  t=k2+1/k2 =", mp.nstr(k2 + 1 / k2, 25),
          " 17/2+15sqrt3/4 =", mp.nstr(mp.mpf(17) / 2 + 15 * mp.sqrt(3) / 4, 25))


if __name__ == "__main__":
    main()
