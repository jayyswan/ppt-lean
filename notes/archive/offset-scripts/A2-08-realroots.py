"""A2-08: real-root patterns of the crossing polynomial Q for random rational data.

For each family we sample random rational parameters, build Q exactly, and count real roots
by Sturm sequences (sympy count_roots).  This is the 'real feasibility by root pattern'
evidence for the DIRECT engine: each real root is a genuine crossing for one sign of d (O4),
hence a P-constructible real number.  Tally how many real roots occur.
"""
import random, sys
import sympy as sp
from collections import Counter

t, w = sp.symbols('t w')
X, Y = sp.symbols('X Y')


def build(x, y, d, F, m):
    xp, yp = sp.diff(x, t), sp.diff(y, t)
    q = sp.expand(xp ** 2 + yp ** 2)
    Fs = sp.expand(F.subs({X: x - d * yp / w, Y: y + d * xp / w}))
    expr = sp.expand(w ** m * Fs)
    p = sp.Poly(expr, w)
    A = sp.Integer(0)
    B = sp.Integer(0)
    for k in range(p.degree() + 1):
        ck = p.coeff_monomial(w ** k)
        if ck == 0:
            continue
        if k % 2 == 0:
            A += ck * q ** (k // 2)
        else:
            B += ck * q ** ((k - 1) // 2)
    A, B = sp.expand(A), sp.expand(B)
    return sp.expand(A ** 2 - B ** 2 * q)


def rat(rng, lo=-6, hi=6):
    return sp.Rational(rng.randint(lo, hi), rng.randint(1, 4))


def gen_base(rng):
    c = [rat(rng) for _ in range(4)]
    e = [rat(rng) for _ in range(4)]
    if c[3] == 0 and e[3] == 0:
        c[3] = 1
    x = c[0] + c[1] * t + c[2] * t ** 2 + c[3] * t ** 3
    y = e[0] + e[1] * t + e[2] * t ** 2 + e[3] * t ** 3
    return x, y, rat(rng, 1, 5)


def sample(name, kind, n, seed):
    rng = random.Random(seed)
    tally = Counter()
    for i in range(n):
        x, y, d = gen_base(rng)
        if kind == 'line':
            A_, B_, C_ = rat(rng), rat(rng), rat(rng)
            if A_ == 0 and B_ == 0:
                A_ = 1
            F, m = A_ * X + B_ * Y - C_, 1
        elif kind == 'conic':
            a, b, c, dd, ee, ff = [rat(rng) for _ in range(6)]
            F, m = a * X ** 2 + b * X * Y + c * Y ** 2 + dd * X + ee * Y + ff, 2
        else:
            g = [rat(rng) for _ in range(4)]
            lam = rat(rng, 1, 5)
            F, m = Y ** 2 - X ** 3 + lam * X ** 2, 3
        Q = build(x, y, d, F, m)
        P = sp.Poly(Q, t)
        if P.degree() < 10 * m:
            continue
        try:
            r = P.count_roots()
        except Exception as ex:
            continue
        tally[int(r)] += 1
    print('%s: n=%d  real-root counts: %s' % (name, sum(tally.values()),
          dict(sorted(tally.items()))))
    sys.stdout.flush()


if __name__ == '__main__':
    sample('F1 line   (N=10)', 'line', 40, 11)
    sample('F2 conic  (N=20)', 'conic', 30, 22)
    sample('F3 cubic  (N=30)', 'cubic', 20, 33)
