"""R2-01: verify V7 (quartic signature) numerically to high precision.

   2F1(1/4, 3/4; 1; z) = (1 + sqrt(z))^(-1/2) * 2F1(1/2, 1/2; 1; 2 sqrt(z)/(1 + sqrt(z)))

Domain of the real identity: z in [0, 1) (the map w = 2 sqrt(z)/(1+sqrt(z)) lies in [0,1)).
Run:  py R2-01-quartic-v7.py
"""
import mpmath as mp

mp.mp.dps = 60


def lhs(z):
    return mp.hyp2f1(mp.mpf(1) / 4, mp.mpf(3) / 4, 1, z)


def rhs(z):
    s = mp.sqrt(z)
    w = 2 * s / (1 + s)
    return (1 + s) ** (mp.mpf(-1) / 2) * mp.hyp2f1(mp.mpf(1) / 2, mp.mpf(1) / 2, 1, w)


def main():
    points = [mp.mpf(1) / 5, mp.mpf(1) / 3, mp.mpf(3) / 4,
              mp.mpf(1) / 100, mp.mpf(1) / 10, mp.mpf(9) / 10, mp.mpf(99) / 100,
              mp.mpf(2) / 7, mp.mpf(1) / 2]
    worst = 0
    print(f"{'z':>10} {'w(z)':>22} {'|lhs-rhs|':>14} {'digits':>7}")
    for z in points:
        s = mp.sqrt(z)
        w = 2 * s / (1 + s)
        diff = abs(lhs(z) - rhs(z))
        digs = -mp.log10(diff) if diff > 0 else mp.inf
        worst = max(worst, diff)
        print(f"{mp.nstr(z, 8):>10} {mp.nstr(w, 20):>22} {mp.nstr(diff, 5):>14} {mp.nstr(digs, 5):>7}")
    print("\nworst absolute error:", mp.nstr(worst, 5))
    print("digits:", mp.nstr(-mp.log10(worst), 5))


if __name__ == "__main__":
    main()
