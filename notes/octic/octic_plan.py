"""Print the construction plan for the real roots of an octic (see GUIDE-octic-cookbook.md).

    python3 octic_plan.py  a8 a7 a6 a5 a4 a3 a2 a1 a0        (integer or decimal coefficients)
    python3 octic_plan.py                                    (runs X^8 - X - 1)

Every line of the output is one of
    COMPUTE  -- arithmetic on numbers already known
    SOLVE6   -- a real root of a polynomial of degree <= 6
    CROSS    -- the one curve crossing
and each is checked numerically before it is printed.  Needs mpmath.
"""

import sys
from mpmath import mp, mpf, mpc, matrix, eigsy, fabs, re, im, sqrt, nstr
from octic_construct import (peval, pmul, roots_of, real_roots, power_sums, companion, charpoly,
                             poly_at_matrix, prem, strip, fit_poly, lagrange_real, CENTRE8, CENTRE8_ROOTS)

mp.dps = 60
N = 8
step_no = [0]


def say(kind, text):
    step_no[0] += 1
    print(f"{step_no[0]:2d}. {kind:7s} {text}")


def fmt(x, d=8):
    return nstr(x, d)


def fpoly(p, var="X", d=6):
    terms = []
    for k, c in enumerate(p):
        if fabs(c) < mpf(10) ** (-40):
            continue
        mon = "" if k == 0 else (var if k == 1 else f"{var}^{k}")
        terms.append(f"({nstr(c, d)}){mon}")
    return " + ".join(terms) if terms else "0"


def padd(u, v, a=1, b=1):
    n = max(len(u), len(v))
    u = list(u) + [mpf(0)] * (n - len(u))
    v = list(v) + [mpf(0)] * (n - len(v))
    return [a * u[i] + b * v[i] for i in range(n)]


def pscale(u, a):
    return [a * c for c in u]


def pprod(*ps):
    out = [mpf(1)]
    for p in ps:
        out = pmul(out, p)
    return out


class Plan:
    def __init__(self, q):
        self.q = q
        self.s = power_sums(q, 40)
        self.rts = roots_of(q)
        self.reals = sorted(re(r) for r in self.rts if fabs(im(r)) < mpf(10) ** (-20))

    def br(self, *ps):
        """<u v w ...> = sum over the roots r of q of u(r) v(r) w(r) ... (from power sums only)."""
        w = pprod(*ps)
        return sum(w[i] * self.s[i] for i in range(len(w)))

    def center(self, u):
        u = list(u) + [mpf(0)] * (N - len(u))
        u[0] -= self.br(u) / N
        return u

    def mono(self, j):
        return self.center([mpf(0)] * j + [mpf(1)])

    def gram(self):
        G = matrix(7, 7)
        for j in range(1, 8):
            for k in range(1, 8):
                G[j - 1, k - 1] = self.s[j + k] - self.s[j] * self.s[k] / N
        return G

    def from7(self, c):
        return self.center([mpf(0)] + [c[i] for i in range(7)])

    def rounded(self, vec7, test):
        """Scale to largest entry 1, round to as few decimals as pass `test`."""
        m = max(fabs(v) for v in vec7)
        for digits in range(2, 30):
            den = 10 ** digits
            r = [mpf(int(mp.nint(v / m * den))) / den for v in vec7]
            p = self.from7(r)
            if test(p):
                return p, digits
        raise RuntimeError("could not round")

    # ------------------------------------------------------------------ complex roots present
    def cone_point(self, E, V):
        col = lambda k: [V[i, k] for i in range(7)]
        e, de = self.rounded(col(0), lambda p: self.br(p, p) < 0)
        f, df = self.rounded(col(6), lambda p: self.br(p, p) > 0)
        say("COMPUTE", f"seed e (rounded eigenvector of G, eigenvalue {fmt(E[0], 4)}):\n"
                       f"            e = {fpoly(e)}\n            check <e^2> = {fmt(self.br(e, e))} < 0")
        say("COMPUTE", f"seed f (rounded eigenvector of G, eigenvalue {fmt(E[6], 4)}):\n"
                       f"            f = {fpoly(f)}\n            check <f^2> = {fmt(self.br(f, f))} > 0")
        a, b, c = self.br(f, f), self.br(e, f), self.br(e, e)
        t = (-b + sqrt(b * b - a * c)) / a
        say("SOLVE6", f"positive root t of  ({fmt(a)}) t^2 + ({fmt(2 * b)}) t + ({fmt(c)}) = 0"
                      f"   [= <f^2> t^2 + 2<ef> t + <e^2>]\n            t = {fmt(t, 15)}")
        P = padd(e, f, 1, t)
        assert fabs(self.br(P, P)) < mpf(10) ** (-30) * max(1, fabs(a))
        say("COMPUTE", f"P = e + t f = {fpoly(P)}\n            (now <P> = 0 and <P^2> = 0)")
        return P

    def two_pairs(self, E, V, P):
        col = lambda k: [V[i, k] for i in range(7)]
        n1, n2, p1, p2 = (self.from7(col(k)) for k in (0, 1, 5, 6))
        e0 = padd(n1, n2, self.br(P, n2), -self.br(P, n1))
        f0 = padd(p1, p2, self.br(P, p2), -self.br(P, p1))
        i0 = max(range(1, 8), key=lambda j: fabs(self.br(P, self.mono(j))))
        u = self.mono(i0)
        c = self.br(P, u)
        fix = lambda r: padd(pscale(r, c), u, 1, -self.br(P, r))
        eb, _ = self.rounded(e0[1:], lambda r: self.br(fix(r), fix(r)) < 0)
        fb, _ = self.rounded(f0[1:], lambda r: self.br(fix(r), fix(r)) > 0)
        e, f = fix(eb), fix(fb)
        assert fabs(self.br(P, e)) < mpf(10) ** (-30) and fabs(self.br(P, f)) < mpf(10) ** (-30)
        say("COMPUTE", f"second pair of seeds, made orthogonal to P.  With u = X^{i0} - s_{i0}/8,"
                       f" c = <P u> = {fmt(c)}:\n"
                       f"            e' = c e0 - <P e0> u,   e0 = {fpoly(eb)}\n"
                       f"            f' = c f0 - <P f0> u,   f0 = {fpoly(fb)}\n"
                       f"            check <e'^2> = {fmt(self.br(e, e))} < 0 < <f'^2> = {fmt(self.br(f, f))},"
                       f"  <P e'> = <P f'> = 0")
        a, b, cc = self.br(f, f), self.br(e, f), self.br(e, e)
        t = (-b + sqrt(b * b - a * cc)) / a
        say("SOLVE6", f"positive root t' of  ({fmt(a)}) t'^2 + ({fmt(2 * b)}) t' + ({fmt(cc)}) = 0"
                      f"   [= <f'^2> t'^2 + 2<e'f'> t' + <e'^2>]\n            t' = {fmt(t, 15)}")
        x = padd(e, f, 1, t)
        say("COMPUTE", f"x = e' + t' f' = {fpoly(x)}\n            (now <x> = <x^2> = <P x> = 0)")
        ca, cb, cc3, cd = self.br(P, P, P), 3 * self.br(P, P, x), 3 * self.br(P, x, x), self.br(x, x, x)
        if fabs(cd) < mpf(10) ** (-40):
            say("COMPUTE", "<x^3> = 0, so phi = x")
            return x
        tau = real_roots([ca, cb, cc3, cd])[0]
        say("SOLVE6", f"a real root tau of  ({fmt(cd)}) tau^3 + ({fmt(cc3)}) tau^2 + ({fmt(cb)}) tau + ({fmt(ca)}) = 0\n"
                      f"            [= <x^3> tau^3 + 3<P x^2> tau^2 + 3<P^2 x> tau + <P^3>]\n"
                      f"            tau = {fmt(tau, 15)}")
        return padd(P, x, 1, tau)

    def one_pair(self, P):
        def sigma(x):
            return padd(pscale(P, self.br(x, x)), x, 1, -2 * self.br(P, x))

        def Phi(x):
            sg = sigma(x)
            return self.br(sg, sg, sg)

        cands = [self.mono(j) for j in range(1, 8)]
        cands += [padd(self.mono(j), self.mono(k), 1, sgn) for j in range(1, 8) for k in range(j + 1, 8)
                  for sgn in (1, -1)]
        vals = [(Phi(c), c) for c in cands]
        pos = [v for v in vals if v[0] > 0]
        neg = [v for v in vals if v[0] < 0]
        how = "two trial polynomials of opposite sign"
        if not pos or not neg:
            # guaranteed fallback (exists_sign_change8): polynomials equal to 1 at one real root,
            # 0 at the other real roots, and a primitive cube root of unity at the complex root
            z = next(r for r in self.rts if im(r) > mpf(10) ** (-20))
            om = mpc(-0.5, sqrt(3) / 2)
            exact = [lagrange_real(self.q, self.rts, xj, z, c)
                     for xj in self.reals[:2] for c in (om, om.conjugate())]
            ev = [(Phi(self.center(d)), d) for d in exact]
            dpe, dme = max(ev, key=lambda v: v[0]), min(ev, key=lambda v: v[0])
            assert dpe[0] > 0 > dme[0]
            dp_, _ = self.rounded(dpe[1][1:], lambda r: Phi(r) > 0)
            dm_, _ = self.rounded(dme[1][1:], lambda r: Phi(r) < 0)
            pos, neg = [(Phi(dp_), dp_)], [(Phi(dm_), dm_)]
            how = ("two polynomials of opposite sign (rounded from: 1 at one real root, 0 at the other"
                   " real roots,\n            -1/2 +- (sqrt(3)/2) i at the complex root)")
        dp, dm = pos[0][1], neg[0][1]
        say("COMPUTE", "with  sigma(d) = <d^2> P - 2 <P d> d  and  Phi(d) = <sigma(d)^3>,"
                       f" {how}:\n"
                       f"            d+ = {fpoly(dp)},   Phi(d+) = {fmt(pos[0][0])} > 0\n"
                       f"            d- = {fpoly(dm)},   Phi(d-) = {fmt(neg[0][0])} < 0")
        delta = padd(dm, dp, 1, -1)
        nodes = [mpf(k) / 6 for k in range(7)]
        V = matrix(7, 7)
        for i, m in enumerate(nodes):
            for k in range(7):
                V[i, k] = m ** k
        Psi = list(mp.lu_solve(V, matrix([Phi(padd(dp, delta, 1, m)) for m in nodes])))
        ms = [m for m in real_roots(Psi) if 0 < m < 1]
        mstar = ms[0]
        say("SOLVE6", "a root m in (0,1) of the sextic  Psi(m) = Phi(d+ + m (d- - d+)):\n"
                      f"            Psi(m) = {fpoly(Psi, 'm')}\n            m = {fmt(mstar, 15)}")
        v = sigma(padd(dp, delta, 1, mstar))
        assert max(fabs(c) for c in v) > mpf(10) ** (-20)
        return v

    def finish_complex(self, phi):
        big = max(fabs(c) for c in phi)
        phi = pscale(phi, 1 / big)                     # harmless rescaling, keeps numbers readable
        for k in (1, 2, 3):
            assert fabs(self.br(*([phi] * k))) < mpf(10) ** (-25), k
        say("COMPUTE", f"phi = {fpoly(phi, d=10)}\n"
                       "            (rescaled so its largest coefficient is 1;  <phi> = <phi^2> = <phi^3> = 0)")
        R = charpoly(poly_at_matrix(phi, companion(self.q)))
        assert all(fabs(R[k]) < mpf(10) ** (-25) for k in (5, 6, 7))
        c = [-R[k] for k in range(5)]
        say("COMPUTE", "resolvent = characteristic polynomial of phi(C) = resultant_X(q(X), y - phi(X)):\n"
                       f"            y^8 = ({fmt(c[4], 10)}) y^4 + ({fmt(c[3], 10)}) y^3 + ({fmt(c[2], 10)}) y^2"
                       f" + ({fmt(c[1], 10)}) y + ({fmt(c[0], 10)})")
        ys_all = real_roots([-c[0], -c[1], -c[2], -c[3], -c[4], 0, 0, 0, 1])
        for beta in self.reals:
            y = peval(phi, beta)
            print(f"\n    --- for the root x ~ {fmt(beta, 12)} ---")
            if fabs(y) < mpf(10) ** (-30):
                say("COMPUTE", "y = 0")
            else:
                sgn = 1 if y > 0 else -1
                others = [sgn * t for t in ys_all if sgn * t > 0 and fabs(t - y) > mpf(10) ** (-15)]
                lo, hi = self.window(fabs(y), others)
                quart = (f"({fmt(c[4], 10)}) X^4 + ({fmt(sgn * c[3], 10)}) X^3 + ({fmt(c[2], 10)}) X^2"
                         f" + ({fmt(sgn * c[1], 10)}) X + ({fmt(c[0], 10)})")
                say("CROSS", f"the curves  Y = X^8  and  Y = {quart}\n"
                             f"            cross exactly once for {lo} <= X <= {hi}, at X = {fmt(fabs(y), 15)};"
                             f"  y = {'' if sgn > 0 else '-'}X = {fmt(y, 15)}")
            self.euclid(phi, y, beta)

    def window(self, y, others):
        """Rational lo < y < hi with no other crossing in [lo, hi]."""
        below = max([t for t in others if t < y], default=mpf(0))
        above = min([t for t in others if t > y], default=2 * y + 1)
        for digits in range(1, 30):
            den = 10 ** digits
            lo = mp.ceil((below + y) / 2 * den) / den
            hi = mp.floor((above + y) / 2 * den) / den
            if below < lo < y < hi < above:
                return nstr(lo, digits + 3), nstr(hi, digits + 3)
        raise RuntimeError("no window")

    def euclid(self, phi, y, beta):
        vals = [peval(phi, r) for r in self.rts]
        if sum(1 for v in vals if fabs(v - y) < mpf(10) ** (-10)) != 1:
            say("SOLVE7", "phi takes the value y at another root too: Euclid does not isolate x.\n"
                          "            x is a root of phi(X) - y (degree <= 7); see the long guide, section 8")
            return
        a, b = strip(self.q), list(phi)
        b[0] -= y
        b = strip(b)
        while True:
            r = prem(a, b)
            if not r:
                break
            a, b = b, r
        x = -b[0] / b[1]
        assert len(b) == 2 and fabs(x - beta) < mpf(10) ** (-15)
        say("COMPUTE", f"Euclid's algorithm on q(X) and phi(X) - y ends with the remainder r1 X + r0;\n"
                       f"            x = -r0 / r1 = {fmt(x, 20)}")
        print(f"            check: q(x) = {nstr(peval(self.q, x), 3)}")

    # ------------------------------------------------------------------ all roots real
    def all_real(self):
        al = self.reals
        V = matrix(N, N)
        for i, a in enumerate(al):
            for k in range(N):
                V[i, k] = a ** k
        names = ["a", "b", "g", "w1", "w2", "w3"]
        inp = {}
        for key in names:
            sol = mp.lu_solve(V, matrix([mpf(v) for v in CENTRE8[key]]))
            inp[key] = self.center([mpf(int(mp.nint(v * 10 ** 8))) / 10 ** 8 for v in sol])
        targets = "\n".join(f"            {k:2s}: values {[nstr(mpf(v), 6) for v in CENTRE8[k]]}\n"
                            f"                -> {fpoly(inp[k], d=9)}" for k in names)
        say("COMPUTE", "six polynomials of degree <= 7: interpolate the listed values at the roots\n"
                       f"            x1 < ... < x8 of q, round the coefficients to 8 decimals, then subtract <.>/8:\n{targets}")
        lam0, x0, mu0, kap0 = CENTRE8_ROOTS
        near = lambda c, t: min(c, key=lambda r: fabs(r - t))

        p1 = fit_poly(lambda l: self.br(*([padd(inp["a"], inp["b"], 1, l)] * 3)), 3)
        lam = near(real_roots(p1), lam0)
        say("SOLVE6", f"the root lambda nearest 0 of the cubic  <(a + lambda b)^3> = 0:\n"
                      f"            {fpoly(p1, 'L')} = 0\n            lambda = {fmt(lam, 15)}")
        P = padd(inp["a"], inp["b"], 1, lam)
        ng = self.br(P, P, inp["g"])
        assert fabs(ng) > mpf(10) ** (-6)
        proj = lambda w: padd(w, inp["g"], 1, -self.br(P, P, w) / ng)
        W1, W2, W3 = proj(inp["w1"]), proj(inp["w2"]), proj(inp["w3"])
        say("COMPUTE", f"P = a + lambda b;   Wj = wj - (<P^2 wj> / <P^2 g>) g  for j = 1,2,3"
                       f"   (<P^2 g> = {fmt(ng)}, must be nonzero)")
        p2 = fit_poly(lambda x: self.br(P, padd(W1, W2, 1, x), padd(W1, W2, 1, x)), 2)
        x = near(real_roots(p2), x0)
        say("SOLVE6", f"the root x nearest 5/3 of the quadratic  <P (W1 + x W2)^2> = 0:\n"
                      f"            {fpoly(p2, 'x')} = 0\n            x = {fmt(x, 15)}")
        q0 = padd(W1, W2, 1, x)

        def cleared(mu):
            d = padd(W3, W1, 1, mu)
            vec = padd(pscale(q0, self.br(P, d, d)), d, 1, -2 * self.br(P, q0, d))
            return self.br(vec, vec, vec)
        p3 = fit_poly(cleared, 6)
        mu = near(real_roots(p3), mu0)
        say("SOLVE6", "the root mu nearest -5322/2915 = -1.8257... of the sextic\n"
                      "            < ( <P d^2> q0 - 2 <P q0 d> d )^3 > = 0,   q0 = W1 + x W2,  d = mu W1 + W3:\n"
                      f"            {fpoly(p3, 'mu')} = 0\n            mu = {fmt(mu, 15)}")
        d = padd(W3, W1, 1, mu)
        dd = self.br(P, d, d)
        assert fabs(dd) > mpf(10) ** (-6)
        v = padd(q0, d, 1, -2 * self.br(P, q0, d) / dd)
        say("COMPUTE", f"v = q0 - (2 <P q0 d> / <P d^2>) d   (<P d^2> = {fmt(dd)}, must be nonzero)")
        p4 = fit_poly(lambda k: self.br(*([padd(P, v, 1, k)] * 5)), 5)
        kap = near(real_roots(p4), kap0)
        say("SOLVE6", f"the root kappa nearest -1 of the quintic  <(P + kappa v)^5> = 0:\n"
                      f"            {fpoly(p4, 'k')} = 0\n            kappa = {fmt(kap, 15)}")
        phi = padd(P, v, 1, kap)
        for k in (1, 3, 5):
            assert fabs(self.br(*([phi] * k))) < mpf(10) ** (-20)
        say("COMPUTE", f"phi = P + kappa v = {fpoly(phi, d=10)}\n"
                       "            (<phi> = <phi^3> = <phi^5> = 0)")
        R = charpoly(poly_at_matrix(phi, companion(self.q)))
        assert all(fabs(R[k]) < mpf(10) ** (-20) for k in (7, 5, 3))
        Q4 = [R[0], R[2], R[4], R[6], mpf(1)]
        c = -R[1]
        say("COMPUTE", "resolvent = characteristic polynomial of phi(C):   Q(y^2) = c y   with\n"
                       f"            Q(X) = X^4 + ({fmt(R[6], 10)}) X^3 + ({fmt(R[4], 10)}) X^2 + ({fmt(R[2], 10)}) X"
                       f" + ({fmt(R[0], 10)}),   c = {fmt(c, 10)}")
        # all crossings of Q(X) = +-c sqrt(X): roots of Q(X)^2 - c^2 X
        sq = pmul(Q4, Q4)
        sq[1] -= c * c
        xs_all = real_roots(sq)
        for beta in al:
            y = peval(phi, beta)
            print(f"\n    --- for the root x ~ {fmt(beta, 12)} ---")
            sgn = 1 if y > 0 else -1
            others = [t for t in xs_all if t > 0 and fabs(t - y * y) > mpf(10) ** (-15)]
            lo, hi = self.window(y * y, others)
            say("CROSS", f"the curves  Y = Q(X)  and  Y = ({fmt(sgn * c, 10)}) sqrt(X)\n"
                         f"            cross exactly once for {lo} <= X <= {hi}, at X = {fmt(y * y, 15)}")
            say("SOLVE6", f"y = {'' if sgn > 0 else '-'}sqrt(X) = {fmt(y, 15)}")
            self.euclid(phi, y, beta)

    # ------------------------------------------------------------------ driver
    def run(self):
        q = self.q
        print("q(X) =", fpoly(q, d=12))
        sep = min(fabs(self.rts[i] - self.rts[j]) for i in range(N) for j in range(i))
        if sep < mpf(10) ** (-12):
            print("q has a repeated root: replace q by gcd(q, q') and q / gcd(q, q') (degree <= 7).")
            return
        print("approximate real roots:", [nstr(r, 10) for r in self.reals], "\n")
        say("COMPUTE", "power sums s_0..s_40 (Newton):  s_0..s_8 = " + ", ".join(fmt(v, 8) for v in self.s[:9]))
        E, V = eigsy(self.gram())
        E = [E[i] for i in range(7)]
        npairs = (N - len(self.reals)) // 2
        assert sum(1 for v in E if v < 0) == npairs
        say("COMPUTE", f"G[j][k] = s_(j+k) - s_j s_k / 8  (j,k = 1..7);  eigenvalues ~ {[nstr(v, 3) for v in E]}\n"
                       f"            {npairs} negative  =>  " +
                       ("CASE 1: all roots real" if npairs == 0 else
                        "CASE 2: one complex pair" if npairs == 1 else
                        "CASE 3: two or more complex pairs"))
        if npairs == 0:
            self.all_real()
        elif npairs == 4:
            print("no real roots")
        else:
            P = self.cone_point(E, V)
            phi = self.one_pair(P) if npairs == 1 else self.two_pairs(E, V, P)
            self.finish_complex(phi)


if __name__ == "__main__":
    if len(sys.argv) == 10:
        coeffs = [mpf(a) for a in sys.argv[1:]]
    else:
        coeffs = [mpf(v) for v in (1, 0, 0, 0, 0, 0, 0, -1, -1)]
    lead = coeffs[0]
    Plan([c / lead for c in reversed(coeffs)]).run()
