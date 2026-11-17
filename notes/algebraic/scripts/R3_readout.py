"""Theorem R linear-algebra read-out on Y1a's quintic.

Parabola base:  Phi = c' + a tau^2 + sum_j delta_j N_j/rho_j,       N_j = b12_j tau - b22_j.
Cubic Bezier:   Phi = c' + a tau^3 + b tau^2 + sum_j delta_j N_j/rho_j.
A nonzero kernel vector over Q gives X = h_0'(tau) + sum_j delta_j (b11_j tau - b12_j)/rho_j.
ND1: partial sums r_k(tau) != 0.  ND2: X not in Q and deg minpoly(X) = n.

Usage: py -3 R3_readout.py parabola|bezier
"""

import itertools
import sys
from fractions import Fraction

from R3_search import NF, Q5, kernel

# Y1a's four forms as (b11, b12, b22) and their rho.
FORMS4 = [
    ((4, Fraction(5, 2), Fraction(9, 4)),
     [Fraction(1, 2), 3, -3, -1, 1]),
    ((Fraction(49, 4), 3, 5),
     [1, Fraction(9, 2), -2, -1, 0]),
    ((Fraction(41, 4), Fraction(27, 4), Fraction(101, 4)),
     [Fraction(-11, 2), Fraction(7, 2), -2, -2, 1]),
    ((Fraction(105, 16), Fraction(67, 16), Fraction(73, 16)),
     [Fraction(-9, 4), Fraction(11, 4), -2, -1, 1]),
]


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


class Field:
    def __init__(self, q):
        self.F = NF([int(x) for x in q])
        self.n = self.F.n

    def vec(self, coeffs):
        v = [Fraction(0)] * self.n
        for i, c in enumerate(coeffs):
            v[i] = Fraction(c)
        return v

    def mul(self, a, b):
        return [Fraction(x) for x in self.F.mul(a, b)]

    def add(self, a, b, sa=1, sb=1):
        return [sa * x + sb * y for x, y in zip(a, b)]

    def inv(self, a):
        cols = []
        for j in range(self.n):
            e = [Fraction(0)] * self.n
            e[j] = Fraction(1)
            cols.append(self.mul(a, e))
        M = [[cols[j][i] for j in range(self.n)] for i in range(self.n)]
        rhs = [Fraction(1)] + [Fraction(0)] * (self.n - 1)
        for c in range(self.n):
            p = next(i for i in range(c, self.n) if M[i][c] != 0)
            M[c], M[p] = M[p], M[c]
            rhs[c], rhs[p] = rhs[p], rhs[c]
            pv = M[c][c]
            M[c] = [x / pv for x in M[c]]
            rhs[c] /= pv
            for i in range(self.n):
                if i != c and M[i][c] != 0:
                    f = M[i][c]
                    M[i] = [M[i][k] - f * M[c][k] for k in range(self.n)]
                    rhs[i] -= f * rhs[c]
        return rhs

    def minpoly(self, x):
        powers = [[Fraction(0)] * self.n for _ in range(self.n + 1)]
        powers[0][0] = Fraction(1)
        for k in range(1, self.n + 1):
            powers[k] = self.mul(powers[k - 1], x)
        rows = [[powers[k][i] for k in range(self.n + 1)] for i in range(self.n)]
        bas = kernel(rows, self.n + 1)
        assert bas, "no relation"
        v = bas[0]
        den = 1
        for z in v:
            den = den * z.denominator // _gcd(den, z.denominator)
        ints = [int(z * den) for z in v]
        lead = ints[-1]
        return [Fraction(z, lead) for z in ints]


def int_poly(coeffs):
    """Primitive integer version of a monic rational polynomial (low -> high)."""
    den = 1
    for z in coeffs:
        den = den * z.denominator // _gcd(den, z.denominator)
    ints = [int(z * den) for z in coeffs]
    g = 0
    for z in ints:
        g = _gcd(g, abs(z))
    ints = [z // g for z in ints]
    if ints[-1] < 0:
        ints = [-z for z in ints]
    return ints


def kernel_vector(Fld, forms, rhos, cubic):
    tau = Fld.vec([0, 1, 0, 0, 0])
    one = Fld.vec([1])
    tau2 = Fld.mul(tau, tau)
    tau3 = Fld.mul(tau2, tau)
    cols = [one, tau3, tau2] if cubic else [one, tau2]
    for (b11, b12, b22), rho in zip(forms, rhos):
        N = [b12 * x for x in tau]
        N[0] -= b22
        cols.append(Fld.mul(N, Fld.inv(rho)))
    rows = [[cols[j][i] for j in range(len(cols))] for i in range(Fld.n)]
    return tau, cols, kernel(rows, len(cols))


def describe(Fld, forms, rhos, vec, cubic):
    tau = Fld.vec([0, 1, 0, 0, 0])
    tau2 = Fld.mul(tau, tau)
    tau3 = Fld.mul(tau2, tau)
    if cubic:
        c0, a, b = vec[0], vec[1], vec[2]
        deltas = vec[3:]
        X = Fld.add([3 * a * x for x in tau2], [2 * b * x for x in tau])
    else:
        c0, a = vec[0], vec[1]
        b = None
        deltas = vec[2:]
        X = [2 * a * x for x in tau]

    phi = [c0 * x for x in Fld.vec([1])]
    if cubic:
        phi = Fld.add(phi, [a * x for x in tau3], 1, 1)
        phi = Fld.add(phi, [b * x for x in tau2], 1, 1)
    else:
        phi = Fld.add(phi, [a * x for x in tau2], 1, 1)
    nums = []
    for j, ((b11, b12, b22), rho) in enumerate(zip(forms, rhos)):
        N = [b12 * x for x in tau]
        N[0] -= b22
        term = Fld.mul(N, Fld.inv(rho))
        nums.append(term)
        phi = Fld.add(phi, term, 1, deltas[j])

    nd1_vals = [[c0 * x for x in Fld.vec([1])]]
    acc = nd1_vals[0]
    for j in range(len(forms)):
        acc = Fld.add(acc, nums[j], 1, deltas[j])
        nd1_vals.append(acc)
    nd1 = all(any(x != 0 for x in v) for v in nd1_vals)

    for j, ((b11, b12, b22), rho) in enumerate(zip(forms, rhos)):
        N2 = [b11 * x for x in tau]
        N2[0] -= b12
        X = Fld.add(X, Fld.mul(N2, Fld.inv(rho)), 1, deltas[j])
    inQ = all(X[i] == 0 for i in range(1, Fld.n))
    mp = None if inQ else Fld.minpoly(X)
    return dict(c0=c0, a=a, b=b, deltas=deltas, nd1=nd1, X_in_Q=inQ,
                minpoly=mp, phi_zero=all(x == 0 for x in phi))


def run(cubic, forms, rhos):
    Fld = Field(Q5)
    tau, cols, bas = kernel_vector(Fld, forms, rhos, cubic)
    print(f"matrix {Fld.n} x {len(cols)}, kernel dim {len(bas)}")
    for vec in bas:
        print("  vector:", [str(x) for x in vec])
        d = describe(Fld, forms, rhos, vec, cubic)
        line = f"   c'={d['c0']}  a={d['a']}"
        if cubic:
            line += f"  b={d['b']}"
        print(line)
        print("   deltas:", [str(x) for x in d["deltas"]])
        print("   Phi=0:", d["phi_zero"], " ND1:", d["nd1"], " X in Q:", d["X_in_Q"])
        if d["minpoly"]:
            print("   minpoly(X):", [str(x) for x in d["minpoly"]],
                  " degree", len(d["minpoly"]) - 1)
            print("   integer minpoly:", int_poly(d["minpoly"]))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "parabola"
    if mode == "parabola":
        print("J=4 parabola on Y1a's four forms")
        run(False, [f for f, _ in FORMS4],
            [[Fraction(x) for x in r] for _, r in FORMS4])
    else:
        for idx in itertools.combinations(range(4), 3):
            print(f"J=3 cubic Bezier on forms {idx}")
            run(True, [FORMS4[i][0] for i in idx],
                [[Fraction(x) for x in FORMS4[i][1]] for i in idx])
            print()
