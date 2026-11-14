"""Reference run of GUIDE-octic-cookbook.md: does exactly what the guide tells the reader to do.

    python3 octic_byhand.py  a8 a7 a6 a5 a4 a3 a2 a1 a0     (trace for one octic)
    python3 octic_byhand.py                                 (trace for X^8 - X - 1)
    python3 octic_byhand.py test                            (success rates on random octics)

Everything is computed from the "value table": each polynomial is recorded by its values at the
eight (approximate) roots of q, and <u v w> is the sum over the roots of the product of values.
Needs mpmath.
"""

import itertools
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

    def gram_schmidt(self, order):
        """Orthogonalise the centred monomials.  A monomial whose pivot comes out 0 is put back
        at the end of the queue; if only zero pivots are left, two of them are added together."""
        basis, queue, stuck = [], [(str(j), self.mono(j)) for j in order], 0
        while queue:
            name, g0 = queue.pop(0)
            g = g0
            for _, h, d in basis:
                g = lin((1, g), (-self.br(g, h) / d, h))
            d = self.br(g, g)
            scale = max(fabs(c) for c in g) ** 2
            if fabs(d) > mpf(10) ** (-12) * max(scale, 1):
                basis.append((name, g, d))
                stuck = 0
                continue
            stuck += 1
            if stuck <= len(queue):
                queue.append((name, g0))             # try again later
            elif queue:
                name2, h0 = queue.pop(0)             # all remaining pivots vanish: add two
                queue.insert(0, (f"{name}+{name2}", lin((1, g0), (1, h0))))
                queue.append((f"{name}-{name2}", lin((1, g0), (-1, h0))))
                stuck = 0
        return basis

    # ------------------------------------------------------------------ Case A
    def case_A(self, order=range(1, 8)):
        basis = self.gram_schmidt(order)
        neg = [b for b in basis if b[2] < 0][:2]
        pos = [b for b in basis if b[2] > 0][:2]
        (ja, ga, da), (jb, gb, db) = neg
        (jc, gc, dc), (jd, gd, dd) = pos
        out("  Gram-Schmidt pivots d_j:", {b[0]: f(b[2], 6) for b in basis})
        out(f"  negative: g{ja}, g{jb};  positive: g{jc}, g{jd}")
        t, t2 = sqrt(-da / dc), sqrt(-db / dd)
        out(f"  SOLVE6  t  = sqrt(-d{ja}/d{jc}) = {f(t, 12)}")
        out(f"  SOLVE6  t' = sqrt(-d{jb}/d{jd}) = {f(t2, 12)}")
        P, x = lin((1, ga), (t, gc)), lin((1, gb), (t2, gd))
        out(f"  P  = g{ja} + t g{jc}  = {fpoly(P)}")
        out(f"  x~ = g{jb} + t' g{jd} = {fpoly(x)}")
        cub = [self.br(P, P, P), 3 * self.br(P, P, x), 3 * self.br(P, x, x), self.br(x, x, x)]
        tau = real_roots(cub)[0]
        out(f"  SOLVE6  cubic ({f(cub[3])}) T^3 + ({f(cub[2])}) T^2 + ({f(cub[1])}) T + ({f(cub[0])}) = 0,"
            f"  tau = {f(tau, 12)}")
        return lin((1, P), (tau, x))

    # ------------------------------------------------------------------ Case B
    def case_B(self, order=range(1, 8)):
        basis = self.gram_schmidt(order)
        ja, ga, da = next(b for b in basis if b[2] < 0)
        pos = [b for b in basis if b[2] > 0]
        pairs = sorted(itertools.permutations(pos, 2),
                       key=lambda p: (max(degree(p[0][1]), degree(p[1][1])), degree(p[0][1])))
        out("  Gram-Schmidt pivots d_j:", {b[0]: f(b[2], 6) for b in basis})
        for (jc, gc, dc), (jd, gd, dd) in pairs:
            t = sqrt(-da / dc)
            U = lin((dc, ga), (-dc * t, gc))
            V = lin((-2 * t * dc, gd))
            W = lin((dd, ga), (dd * t, gc))
            b = self.br
            Psi = [b(U, U, U), 3 * b(U, U, V), 3 * b(U, U, W) + 3 * b(U, V, V), b(V, V, V) + 6 * b(U, V, W),
                   3 * b(V, V, W) + 3 * b(U, W, W), 3 * b(V, W, W), b(W, W, W)]
            ms = real_roots(Psi)
            if not ms:
                out(f"  pair (c, d) = ({jc}, {jd}): sextic has no real root, next pair")
                continue
            m = min(ms, key=fabs)
            out(f"  negative: g{ja};  positive pair used: c = {jc}, d = {jd}")
            out(f"  SOLVE6  t = sqrt(-d{ja}/d{jc}) = {f(t, 12)}")
            out(f"  U = {fpoly(U)}\n  V = {fpoly(V)}\n  W = {fpoly(W)}")
            out(f"  SOLVE6  sextic {fpoly(Psi, 'm')} = 0,  m = {f(m, 12)}")
            return lin((1, U), (m, V), (m * m, W))
        return None

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
    def case_C(self, order=(1, 2, 3, 4, 5, 6), trace=True):
        b = self.br
        a, bb, g, w1, w2, w3 = (self.mono(j) for j in order)
        cub = [b(a, a, a), 3 * b(a, a, bb), 3 * b(a, bb, bb), b(bb, bb, bb)]
        for lam in real_roots(cub):
            P = lin((1, a), (lam, bb))
            ng = b(P, P, g)
            if fabs(ng) < mpf(10) ** (-9):
                continue
            W1, W2, W3 = (lin((1, w), (-b(P, P, w) / ng, g)) for w in (w1, w2, w3))
            quad = [b(P, W1, W1), 2 * b(P, W1, W2), b(P, W2, W2)]
            for xi in real_roots(quad):
                q0 = lin((1, W1), (xi, W2))
                A, B, C = b(P, W1, W1), b(P, W1, W3), b(P, W3, W3)
                E1, E0 = b(P, q0, W1), b(P, q0, W3)
                N0 = lin((C, q0), (-2 * E0, W3))
                N1 = lin((2 * B, q0), (-2 * E0, W1), (-2 * E1, W3))
                N2 = lin((A, q0), (-2 * E1, W1))
                sext = [b(N0, N0, N0), 3 * b(N0, N0, N1), 3 * b(N0, N0, N2) + 3 * b(N0, N1, N1),
                        b(N1, N1, N1) + 6 * b(N0, N1, N2), 3 * b(N1, N1, N2) + 3 * b(N0, N2, N2),
                        3 * b(N1, N2, N2), b(N2, N2, N2)]
                for mu in real_roots(sext):
                    v = lin((1, N0), (mu, N1), (mu * mu, N2))
                    if max(fabs(c) for c in v) < mpf(10) ** (-12):
                        continue
                    vs = max(fabs(c) for c in v)
                    v = [c / vs for c in v]
                    quint = [b(P, P, P, P, P), 5 * b(P, P, P, P, v), 10 * b(P, P, P, v, v),
                             10 * b(P, P, v, v, v), 5 * b(P, v, v, v, v), b(v, v, v, v, v)]
                    for kap in real_roots(quint):
                        phi = lin((1, P), (kap, v))
                        big = max(fabs(c) for c in phi)
                        phi = [c / big for c in phi]
                        ys = [peval(phi, x) for x in self.reals]
                        if min(fabs(ys[i] - ys[j]) for i in range(N) for j in range(i)) < mpf(10) ** (-6):
                            continue
                        for k in (1, 3, 5):
                            assert fabs(self.br_exact(*([phi] * k))) < mpf(10) ** (-20), k
                        out(f"  seeds (a, b, g, w1, w2, w3) = centred X^{order}")
                        out(f"  SOLVE6  cubic {fpoly(cub, 'L')} = 0,  lambda = {f(lam, 12)}")
                        out(f"  <P^2 g> = {f(ng)}")
                        out(f"  SOLVE6  quadratic {fpoly(quad, 'x')} = 0,  xi = {f(xi, 12)}")
                        out(f"  SOLVE6  sextic {fpoly(sext, 'u')} = 0,  mu = {f(mu, 12)}")
                        out(f"  SOLVE6  quintic {fpoly(quint, 'k')} = 0,  kappa = {f(kap, 12)}")
                        out(f"  phi (divided by its largest coefficient) = {fpoly(phi, d=10)}")
                        return phi
        return None

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
            phi = self.case_B()
            return ("B", phi is not None and self.finish_AB(phi))
        orders = [(1, 2, 3, 4, 5, 6)] + [o for o in itertools.permutations(range(1, 7), 6)][1:40]
        for tries, order in enumerate(orders):
            phi = self.case_C(order)
            if phi is not None:
                return ("C", self.finish_C(phi), tries)
            out(f"  seeds in order {order}: no admissible roots, next order")
        return ("C", False, None)


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
            extra = ""
            if kind == "C":
                extra = f";  first seed order worked in {sum(1 for x in res if x[2] == 0)}"
            print(f"Case {kind}: {good} of {n} fully constructed{extra}")
    else:
        coeffs = [mpf(a) for a in sys.argv[1:]] if len(sys.argv) == 10 else \
            [mpf(v) for v in (1, 0, 0, 0, 0, 0, 0, -1, -1)]
        Octic([c / coeffs[0] for c in reversed(coeffs)]).run()
