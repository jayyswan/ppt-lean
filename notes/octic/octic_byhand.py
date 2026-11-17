"""Reference run of GUIDE-octic-cookbook.md: does exactly what the guide tells the reader to do.

    python3 octic_byhand.py  a8 a7 a6 a5 a4 a3 a2 a1 a0     (trace for one octic)
    python3 octic_byhand.py                                 (trace for X^8 - X - 1)
    python3 octic_byhand.py test                            (success rates on random octics)

Everything is computed from the "value table": each polynomial is recorded by its values at the
eight (approximate) roots of q, and <u v w> is the sum over the roots of the product of values.
Needs mpmath.
"""

import random
import sys
from mpmath import mp, mpf, mpc, fabs, re, im, sqrt, nstr
from octic_construct import peval, pmul, roots_of, real_roots, power_sums

mp.dps = 60
N = 8
TINY = mpf(10) ** (-25)
QUIET = [False]


def out(*a):
    if not QUIET[0]:
        print(*a)


def f(x, d=8):
    return nstr(re(x), d)


def fpoly(p, var="X", d=7):
    t = [f"({nstr(c, d)})" + ("" if k == 0 else var if k == 1 else f"{var}^{k}")
         for k, c in enumerate(p) if fabs(c) > mpf(10) ** (-30)]
    return " + ".join(t) if t else "0"


def lin(*terms):
    """Linear combination of polynomials: lin((c1, p1), (c2, p2), ...)."""
    n = max(len(p) for _, p in terms)
    return [sum(c * (p[i] if i < len(p) else 0) for c, p in terms) for i in range(n)]


def degree(p):
    return max(k for k, c in enumerate(p) if fabs(c) > TINY)


class Octic:
    def __init__(self, q):
        self.q = q
        self.r = roots_of(q)
        self.reals = sorted(re(x) for x in self.r if fabs(im(x)) < mpf(10) ** (-20))
        self.pairs = (N - len(self.reals)) // 2
        self.tol = mpf(10) ** (-15)
        self.s_exact = power_sums(q, 60)

    def col(self, u):
        return [peval(u, mpc(x)) for x in self.r]

    def br(self, *us):
        """<u v w ...> from the value table."""
        cols = [self.col(u) for u in us]
        tot = mpc(0)
        for i in range(N):
            term = mpc(1)
            for c in cols:
                term *= c[i]
            tot += term
        return re(tot)

    def br_exact(self, *us):
        """The same bracket from power sums only (independent check)."""
        w = [mpf(1)]
        for u in us:
            w = pmul(w, u)
        return sum(w[i] * self.s_exact[i] for i in range(len(w)))

    def mono(self, j):
        m = [mpf(0)] * j + [mpf(1)]
        m[0] = -self.br(m) / N
        return m

    # ---------------------------------------------------- vectors for the nonreal pairs
    def pair_vector(self, z):
        """e = (A0 + A1 X) * q6(X), q6 = q / (X^2 - 2 a X + a^2 + b^2), z = a + b i a nonreal root.
        e vanishes at the other six roots and has a purely imaginary value at z."""
        a, b = re(z), im(z)
        q6 = list(self.q)                                   # long division by X^2 - 2aX + (a^2+b^2)
        quo = []
        for _ in range(6 + 1):
            c = q6[-1]
            quo.append(c)
            q6[-2] += 2 * a * c
            q6[-3] -= (a * a + b * b) * c
            q6.pop()
        q6 = list(reversed(quo))
        w = peval(q6, mpc(z))
        w1, w2 = re(w), im(w)
        e = pmul([b * w2 - a * w1, w1], q6)
        s = im(peval(e, mpc(z)))                            # e(z) = i s; rescale so that e(z) = i
        return [c / s for c in e]

    def nonreal_setup(self):
        ups = sorted((z for z in self.r if im(z) > mpf(10) ** (-20)), key=lambda z: re(z))
        es = [self.pair_vector(z) for z in ups]
        self.ups = ups
        ds = [self.br(e, e) for e in es]
        assert all(fabs(d + 2) < self.tol for d in ds)      # <e e> = -2 for every pair
        # two positive, orthogonal vectors orthogonal to every e: from the centred X and X^2
        def clean(m):                                       # make m(z) real at every pair
            for z, e in zip(ups, es):
                m = lin((1, m), (-im(peval(m, mpc(z))), e))
            return m
        gc = clean(self.mono(1))
        h = clean(self.mono(2))
        dc = self.br(gc, gc)
        gd = lin((1, h), (-self.br(h, gc) / dc, gc))
        dd = self.br(gd, gd)
        assert dc > 0 and dd > 0
        return es, ds, (gc, dc), (gd, dd)

    # ------------------------------------------------------------------ Case A
    def case_A(self):
        es, ds, (gc, dc), (gd, dd) = self.nonreal_setup()
        out(f"  pair vectors e_k have <e^2> = {[f(d, 6) for d in ds]};  <gc^2> = {f(dc, 6)}, <gd^2> = {f(dd, 6)}")
        t, t2 = sqrt(-ds[0] / dc), sqrt(-ds[1] / dd)
        P, R = lin((1, es[0]), (t, gc)), lin((1, es[1]), (t2, gd))
        cub = [self.br(P, P, P), 3 * self.br(P, P, R), 3 * self.br(P, R, R), self.br(R, R, R)]
        if fabs(cub[3]) < mpf(10) ** (-15) * max(fabs(c) for c in cub):
            return R
        tau = real_roots(cub)[0]
        out(f"  SOLVE6  cubic ({f(cub[3])}) T^3 + ({f(cub[2])}) T^2 + ({f(cub[1])}) T + ({f(cub[0])}) = 0,"
            f"  tau = {f(tau, 12)}")
        return lin((1, P), (tau, R))

    # ------------------------------------------------------------------ Case B
    def case_B(self):
        es, ds, (gc, dc), (gd, dd) = self.nonreal_setup()
        ga, da = es[0], ds[0]
        t = sqrt(-da / dc)
        U = lin((dc, ga), (-dc * t, gc))
        V = lin((-2 * t * dc, gd))
        W = lin((dd, ga), (dd * t, gc))
        b = self.br
        Psi = [b(U, U, U), 3 * b(U, U, V), 3 * b(U, U, W) + 3 * b(U, V, V), b(V, V, V) + 6 * b(U, V, W),
               3 * b(V, V, W) + 3 * b(U, W, W), 3 * b(V, W, W), b(W, W, W)]
        if fabs(Psi[6]) < mpf(10) ** (-15) * max(fabs(c) for c in Psi):
            return W
        ms = real_roots(Psi)
        assert ms, "sextic has no real root (this should never happen)"
        m = min(ms, key=fabs)
        out(f"  SOLVE6  sextic {fpoly(Psi, 'm')} = 0,  m = {f(m, 12)}")
        return lin((1, U), (m, V), (m * m, W))

    def finish_AB(self, phi):
        big = max(fabs(c) for c in phi)
        phi = [c / big for c in phi]
        for k in (1, 2, 3):
            assert fabs(self.br_exact(*([phi] * k))) < mpf(10) ** (-20), k
        assert degree(phi) >= 1
        out(f"  phi (divided by its largest coefficient) = {fpoly(phi, d=10)}")
        p = [None] + [self.br(*([phi] * k)) for k in range(1, 9)]
        c = [p[8] / 8 - p[4] ** 2 / 32, p[7] / 7, p[6] / 6, p[5] / 5, p[4] / 4]
        out("  power sums of the values:  " + ", ".join(f"p{k} = {f(p[k], 9)}" for k in range(4, 9)))
        out(f"  reduced equation:  y^8 = ({f(c[4], 10)}) y^4 + ({f(c[3], 10)}) y^3 + ({f(c[2], 10)}) y^2"
            f" + ({f(c[1], 10)}) y + ({f(c[0], 10)})")
        ok = True
        for x0 in self.reals:
            y = peval(phi, x0)
            assert fabs(y ** 8 - sum(c[k] * y ** k for k in range(5))) < mpf(10) ** (-20) * max(1, y ** 8)
            ok &= self.recover(phi, y, x0)
        return ok

    def recover(self, phi, y, x0):
        out(f"  --- root x ~ {f(x0, 10)}:  y = phi(x) = {f(y, 12)}")
        rec = list(phi)
        rec[0] -= y
        what = "phi(X) = y"
        if degree(phi) == 7:
            # one division step: q = (linear) * (phi - y) + rem, and rem has degree <= 6
            rem = list(self.q)
            for _ in range(2):
                k = len(rem) - 8
                fac = rem[-1] / rec[7]
                for i in range(8):
                    rem[k + i] -= fac * rec[i]
                rem.pop()
            assert max(fabs(c) for c in rem) > mpf(10) ** (-12)
            rec = rem
            what = "rem(X) = 0, rem = remainder of q divided by phi - y,"
        cands = real_roots(rec)
        x = min(cands, key=lambda v: fabs(v - x0))
        assert fabs(x - x0) < mpf(10) ** (-15), (x, x0)
        out(f"      SOLVE6  {what}  (degree {degree(rec)}; real roots {[f(v, 6) for v in cands]}),"
            f"  x = {f(x, 15)}")
        return True

    # ------------------------------------------------------------------ Case C
    CENTRE = dict(
        a=[-4, -2, 2, -1, 1, 4, 1, -1],
        b=[0, 3, 0, 2, 1, -1, -6, 1],
        g=[1, mpf(-2) / 3, 0, -1, 1, mpf(3) / 2, mpf(2) / 3, mpf(-5) / 2],
        w1=[mpf(-143) / 21, mpf(-113) / 21, mpf(-22) / 21, mpf(-452) / 63, mpf(-18) / 7,
            mpf(170) / 21, mpf(-24) / 7, mpf(1154) / 63],
        w2=[mpf(38) / 35, mpf(29) / 35, mpf(1) / 35, mpf(137) / 105, mpf(96) / 35, mpf(-44) / 35,
            mpf(156) / 35, mpf(-193) / 21],
        w3=[mpf(167) / 35, mpf(-89) / 35, mpf(184) / 35, mpf(-272) / 105, mpf(-501) / 35,
            mpf(-186) / 35, mpf(-101) / 35, mpf(370) / 21],
    )
    NOMINAL = (mpf(0), mpf(5) / 3, mpf(-5322) / 2915, mpf(-1))

    def lagrange_table(self):
        """Column i = coefficients of q(X) / ((X - r_i) q'(r_i)), low to high."""
        cols = []
        for a in self.reals:
            c = [mpf(0)] * 8
            carry = mpf(0)
            for k in range(8, 0, -1):
                carry = self.q[k] + carry * a
                c[k - 1] = carry
            dq = peval(c, a)
            cols.append([x / dq for x in c])
        return cols

    def seed(self, cols, Y, digits):
        poly = [sum(Y[i] * cols[i][k] for i in range(N)) for k in range(8)]
        scale = mpf(10) ** digits
        poly = [mpf(int(mp.nint(v * scale))) / scale for v in poly]
        poly[0] -= self.br(poly) / N                      # make the trace exactly zero
        return poly

    def case_C(self, digits=10):
        b = self.br
        cols = self.lagrange_table()
        a, bb, g, w1, w2, w3 = (self.seed(cols, [mpf(v) for v in self.CENTRE[k]], digits)
                                for k in ("a", "b", "g", "w1", "w2", "w3"))
        near = lambda rs, t: min(rs, key=lambda r: fabs(r - t))
        lam0, xi0, mu0, kap0 = self.NOMINAL
        cub = [b(a, a, a), 3 * b(a, a, bb), 3 * b(a, bb, bb), b(bb, bb, bb)]
        lam = near(real_roots(cub), lam0)
        P = lin((1, a), (lam, bb))
        ng = b(P, P, g)
        W1, W2, W3 = (lin((1, w), (-b(P, P, w) / ng, g)) for w in (w1, w2, w3))
        quad = [b(P, W1, W1), 2 * b(P, W1, W2), b(P, W2, W2)]
        xi = near(real_roots(quad), xi0)
        q0 = lin((1, W1), (xi, W2))
        A, B, C = b(P, W1, W1), b(P, W1, W3), b(P, W3, W3)
        E1, E0 = b(P, q0, W1), b(P, q0, W3)
        N0 = lin((C, q0), (-2 * E0, W3))
        N1 = lin((2 * B, q0), (-2 * E0, W1), (-2 * E1, W3))
        N2 = lin((A, q0), (-2 * E1, W1))
        sext = [b(N0, N0, N0), 3 * b(N0, N0, N1), 3 * b(N0, N0, N2) + 3 * b(N0, N1, N1),
                b(N1, N1, N1) + 6 * b(N0, N1, N2), 3 * b(N1, N1, N2) + 3 * b(N0, N2, N2),
                3 * b(N1, N2, N2), b(N2, N2, N2)]
        mu = near(real_roots(sext), mu0)
        den = A * mu * mu + 2 * B * mu + C
        v = lin((1 / den, N0), (mu / den, N1), (mu * mu / den, N2))
        quint = [b(P, P, P, P, P), 5 * b(P, P, P, P, v), 10 * b(P, P, P, v, v),
                 10 * b(P, P, v, v, v), 5 * b(P, v, v, v, v), b(v, v, v, v, v)]
        kap = near(real_roots(quint), kap0)
        roots = (lam, xi, mu, kap)
        assert all(fabs(r - t) < mpf(10) ** (-3) for r, t in zip(roots, self.NOMINAL)), roots
        phi = lin((1, P), (kap, v))
        big = max(fabs(c) for c in phi)
        phi = [c / big for c in phi]
        for k in (1, 3, 5):
            assert fabs(self.br_exact(*([phi] * k))) < self.tol, k
        out(f"  SOLVE6  cubic root nearest 0:  lambda = {f(lam, 12)}")
        out(f"  Arithmetic  quadratic root nearest 5/3:  xi = {f(xi, 12)}")
        out(f"  SOLVE6  sextic root nearest -1.8257:  mu = {f(mu, 12)}")
        out(f"  SOLVE6  quintic root nearest -1:  kappa = {f(kap, 12)}")
        out(f"  phi (divided by its largest coefficient) = {fpoly(phi, d=10)}")
        return phi

    def finish_C(self, phi):
        p = [None] + [self.br(*([phi] * k)) for k in range(1, 9)]
        e2 = -p[2] / 2
        e4 = (-e2 * p[2] - p[4]) / 4
        e6 = (-e4 * p[2] - e2 * p[4] - p[6]) / 6
        e8 = (-e6 * p[2] - e4 * p[4] - e2 * p[6] - p[8]) / 8
        c = p[7] / 7
        Q = [e8, e6, e4, e2, mpf(1)]
        out("  power sums of the values:  " + ", ".join(f"p{k} = {f(p[k], 9)}" for k in (2, 4, 6, 7, 8)))
        out(f"  reduced equation:  Q(y^2) = c y,  Q(X) = X^4 + ({f(e2, 10)}) X^3 + ({f(e4, 10)}) X^2"
            f" + ({f(e6, 10)}) X + ({f(e8, 10)}),  c = {f(c, 10)}")
        ok = True
        for x0 in self.reals:
            y = peval(phi, x0)
            assert fabs(peval(Q, y * y) - c * y) < mpf(10) ** (-20) * max(1, y ** 8)
            ok &= self.recover(phi, y, x0)
        return ok

    def run(self):
        out("q(X) =", fpoly(self.q, d=12))
        out("roots:", [nstr(x, 8) for x in self.r])
        if self.pairs == 4:
            out("no real roots")
            return None
        out(f"{len(self.reals)} real roots  =>  Case {'C' if self.pairs == 0 else 'B' if self.pairs == 1 else 'A'}")
        if self.pairs >= 2:
            return ("A", self.finish_AB(self.case_A()))
        if self.pairs == 1:
            return ("B", self.finish_AB(self.case_B()))
        return ("C", self.finish_C(self.case_C()))


def random_octic(rng, kind):
    while True:
        if kind == "A":
            q = [mpf(rng.randint(-5, 5)) for _ in range(8)] + [mpf(1)]
        else:
            k = 6 if kind == "B" else 8
            p = [mpf(1)]
            for x in rng.sample(range(-6, 7), k):
                p = pmul(p, [mpf(-x), mpf(1)])
            if kind == "B":
                p = pmul(p, [mpf(rng.randint(1, 5)), mpf(rng.randint(-2, 2)), mpf(1)])
            p[rng.randint(0, 3)] += rng.choice([-1, 1])
            q = p
        o = Octic(q)
        sep = min(fabs(o.r[i] - o.r[j]) for i in range(N) for j in range(i))
        want = {"A": (2, 3), "B": (1,), "C": (0,)}[kind]
        if sep > mpf(10) ** (-6) and o.pairs in want:
            return o


if __name__ == "__main__":
    if len(sys.argv) == 2 and sys.argv[1] == "test":
        QUIET[0] = True
        rng = random.Random(2024)
        for kind, n in (("A", 60), ("B", 60), ("C", 30)):
            res = [random_octic(rng, kind).run() for _ in range(n)]
            good = sum(1 for x in res if x[1])
            print(f"Case {kind}: {good} of {n} fully constructed, no alternative choices tried")
    else:
        coeffs = [mpf(a) for a in sys.argv[1:]] if len(sys.argv) == 10 else \
            [mpf(v) for v in (1, 0, 0, 0, 0, 0, 0, -1, -1)]
        Octic([c / coeffs[0] for c in reversed(coeffs)]).run()
