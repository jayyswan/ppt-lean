"""A2-06-dim2: general dimension engine (base curve and implicit second curve both symbolic
in the family parameters) and the Bezier-cubic second curve (F3, legal version)."""
import random, sys, sympy as sp
from sympy import expand, diff, Integer, symbols

P = 2 ** 61 - 1


class D:
    __slots__ = ('v', 'g')

    def __init__(self, v, g):
        self.v = v % P
        self.g = [x % P for x in g]

    def __add__(self, o):
        if isinstance(o, int):
            return D(self.v + o, self.g)
        return D(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])

    __radd__ = __add__

    def __neg__(self):
        return D(-self.v, [-a for a in self.g])

    def __sub__(self, o):
        if isinstance(o, int):
            return D(self.v - o, self.g)
        return D(self.v - o.v, [a - b for a, b in zip(self.g, o.g)])

    def __mul__(self, o):
        if isinstance(o, int):
            return D(self.v * o, [a * o for a in self.g])
        n = len(self.g)
        return D(self.v * o.v, [self.v * o.g[k] + o.v * self.g[k] for k in range(n)])

    __rmul__ = __mul__

    def __pow__(self, n):
        r = D(1, [0] * len(self.g))
        b = self
        while n:
            if n & 1:
                r = r * b
            b = b * b
            n >>= 1
        return r


def rmul(X, Y, q):
    A1, B1 = X
    A2, B2 = Y
    return (A1 * A2 + B1 * B2 * q, A1 * B2 + A2 * B1)


def rpow(X, e, q):
    r = (D(1, [0] * len(q.g)), D(0, [0] * len(q.g)))
    b = X
    while e:
        if e & 1:
            r = rmul(r, b, q)
        b = rmul(b, b, q)
        e >>= 1
    return r


def wpow(e, q, n):
    if e % 2 == 0:
        return (q ** (e // 2), D(0, [0] * n))
    return (D(0, [0] * n), q ** ((e - 1) // 2))


def gf_rank(rows, prime=P):
    M = [r[:] for r in rows]
    ncol = len(M[0]) if M else 0
    rank = 0
    for col in range(ncol):
        piv = next((i for i in range(rank, len(M)) if M[i][col] % prime), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col] % prime, -1, prime)
        M[rank] = [(v * inv) % prime for v in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col] % prime:
                f = M[i][col] % prime
                Mr = M[rank]
                M[i] = [(M[i][k] - f * Mr[k]) % prime for k in range(ncol)]
        rank += 1
        if rank == len(M):
            break
    return rank


class Fam:
    def __init__(self, name, params, x, y, d, m, terms):
        self.name = name
        self.params = params
        self.x = x
        self.y = y
        self.d = d
        self.m = m
        self.terms = terms  # list (coef_expr, i, j)

    def prep(self):
        names = self.params
        E = {}
        for e in [self.x, self.y, diff(self.x, T), diff(self.y, T), self.d] + [c for c, _, _ in self.terms]:
            E[e] = [expand(diff(e, p)) for p in names]
        self.E = E
        self.idx = {p: k for k, p in enumerate(names)}

    @staticmethod
    def imod(expr, sub):
        r = sp.Rational(expr.subs(sub))
        return int(r.p) * pow(int(r.q) % P, -1, P) % P

    def val(self, expr, vals, tv, n):
        sub = {p: vals[p] for p in self.params}
        sub[T] = tv
        return D(self.imod(expr, sub), [self.imod(e, sub) for e in self.E[expr]] + [0])

    def dt(self, expr, vals, tv, n):
        # partial wrt t (last gradient slot)
        sub = {p: vals[p] for p in self.params}
        sub[T] = tv
        return D(self.imod(expr, sub),
                 [self.imod(e, sub) for e in self.E[expr]] + [self.imod(diff(expr, T), sub)])

    def Q(self, vals, tv):
        n = len(self.params) + 1
        x = self.dt(self.x, vals, tv, n)
        y = self.dt(self.y, vals, tv, n)
        xp = self.dt(diff(self.x, T), vals, tv, n)
        yp = self.dt(diff(self.y, T), vals, tv, n)
        d = self.val(self.d, vals, tv, n)
        q = xp ** 2 + yp ** 2
        al = (-d * yp, x)
        be = (d * xp, y)
        tot = (D(0, [0] * n), D(0, [0] * n))
        for (coef, i, j) in self.terms:
            c = self.val(coef, vals, tv, n)
            e = self.m - i - j
            term = rpow(al, i, q)
            term = rmul(term, rpow(be, j, q), q)
            wa, wb = wpow(e, q, n)
            term = (term[0] * wa + term[1] * wb * q, term[0] * wb + term[1] * wa)
            tot = (tot[0] + c * term[0], tot[1] + c * term[1])
        A, B = tot
        return A * A - B * B * q

    def dims(self, seed=0):
        self.prep()
        n = len(self.params) + 1
        N = 10 * self.m
        random.seed(seed)
        vals = {p: random.randint(1, P - 1) for p in self.params}
        ts = random.sample(range(1, P), N + 1)
        Mplain, Mfull = [], []
        for tv in ts:
            Q = self.Q(vals, tv)
            dq = Q.g[-1]
            pl = Q.g[:-1]
            Mplain.append(pl)
            Mfull.append(pl + [dq, tv * dq % P, tv * tv % P * dq % P])
        return gf_rank(Mplain), gf_rank(Mfull), self.m, N, len(self.params)


T = symbols('t')


def syms(names):
    return symbols(names)


def main():
    c = symbols('c0:4')
    e = symbols('e0:4')
    A, B, C = symbols('A B C')
    aa, bb, cc, dd, ee, ff = symbols('aa bb cc dd ee ff')
    x = c[0] + c[1] * T + c[2] * T ** 2 + c[3] * T ** 3
    y = e[0] + e[1] * T + e[2] * T ** 2 + e[3] * T ** 3
    base = list(c) + list(e) + [sp.Symbol('d')]
    X, Y = symbols('X Y')

    # conic
    f_conic = Fam('conic', base + [aa, bb, cc, dd, ee, ff], x, y, sp.Symbol('d'), 2,
                  [(aa, 2, 0), (bb, 1, 1), (cc, 0, 2), (dd, 1, 0), (ee, 0, 1), (-ff, 0, 0)])
    # graph degree 6
    h = symbols('h0:7')
    terms_g6 = [(Integer(1), 0, 1)] + [(-h[k], k, 0) for k in range(7)]
    f_g6 = Fam('graph6', base + list(h), x, y, sp.Symbol('d'), 6, terms_g6)

    # Bezier cubic: affine image of nodal cubic Y^2 = X^3 - lam X^2
    lam, u, v, sx, sy, tx, ty = symbols('lam u v sx sy tx ty')
    # linear part = Rot * Diag  (rotate then independent scale), up to the scale of (u,v)
    Minv = sp.Matrix([[u, v], [-v, u]]) * sp.Matrix([[1 / sx, 0], [0, 1 / sy]])
    Xl = Minv[0, 0] * (X - tx) + Minv[0, 1] * (Y - ty)
    Yl = Minv[1, 0] * (X - tx) + Minv[1, 1] * (Y - ty)
    Fb = expand(Yl ** 2 - Xl ** 3 + lam * Xl ** 2)
    Fb = sp.numer(sp.together(Fb))
    terms_b = []
    Fbe = expand(Fb)
    for i in range(4):
        for j in range(4 - i):
            cf = Fbe.coeff(X, i).coeff(Y, j)
            if cf != 0:
                terms_b.append((expand(cf), i, j))
    bez = base + [lam, u, v, sx, sy, tx, ty]
    f_bez = Fam('bezier_cubic', bez, x, y, sp.Symbol('d'), 3, terms_b)

    for F in [f_conic, f_g6, f_bez]:
        try:
            rp, rf, m, N, npr = F.dims()
            print('%-14s m=%d N=%3d npar=%2d rank=%2d D=%2d codimP=%3d Dsat=%2d' %
                  (F.name, m, N, npr, rp, rp - 1, N - (rp - 1), rf - 1))
        except Exception as ex:
            import traceback
            print(F.name, 'ERR', ex)
            traceback.print_exc()
        sys.stdout.flush()


if __name__ == '__main__':
    main()
