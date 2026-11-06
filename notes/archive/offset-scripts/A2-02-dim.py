"""A2-02-dim: fast Jacobian rank of the offset-crossing family, via mod-p dual numbers.

For a numeric t and numeric parameter values we evaluate Q(t) = A^2 - B^2 q, where
w^m F(Gamma) = A + B w and w = sqrt(q), directly in the ring F_p[w]/(w^2 - q), carrying
first derivatives wrt every family parameter (dual numbers).  Evaluating at N+1 distinct
t-values turns coefficient-space rank into rank of the evaluation matrix.  Adds the three
sl2 (Mobius-tangent) directions t^k Q'(t), k=0,1,2 to get the PGL2-saturated rank.
"""
import random, sys

P = 2 ** 61 - 1
NE = 0


class D:
    __slots__ = ('v', 'g')

    def __init__(self, v, g):
        self.v = v % P
        self.g = [x % P for x in g]

    def __add__(self, o):
        if isinstance(o, int):
            return D(self.v + o, self.g)
        return D(self.v + o.v, [a + b for a, b in zip(self.g, o.g)])

    def __radd__(self, o):
        return self.__add__(o)

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

    def __rmul__(self, o):
        return self.__mul__(o)

    def __pow__(self, n):
        r = D(1, [0] * len(self.g))
        b = self
        while n:
            if n & 1:
                r = r * b
            b = b * b
            n >>= 1
        return r


def Dzero(n):
    return D(0, [0] * n)


def emulate(coeffs):
    """ZERO (D) if all coeffs zero else the unit-vector parameter dual."""
    v = coeffs['v']
    return D(v, coeffs['g'])


def rmul(X, Y, q):
    A1, B1 = X
    A2, B2 = Y
    return (A1 * A2 + B1 * B2 * q, A1 * B2 + A2 * B1)


def rpow(X, e, q):
    r = (D(1, [0] * len(q.g)), Dzero(len(q.g)))
    b = X
    while e:
        if e & 1:
            r = rmul(r, b, q)
        b = rmul(b, b, q)
        e >>= 1
    return r


def wpow(e, q, n):
    """Return (A,B) with A + B w = w^e, using w^2 = q."""
    if e % 2 == 0:
        return (q ** (e // 2), Dzero(n))
    return (Dzero(n), q ** ((e - 1) // 2))


def gf_rank(rows, prime=P):
    if not rows:
        return 0
    M = [r[:] for r in rows]
    ncol = len(M[0])
    rank = 0
    for col in range(ncol):
        piv = None
        for i in range(rank, len(M)):
            if M[i][col] % prime:
                piv = i
                break
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


def build_family(name):
    """Return dict: params(list of names), m, term=lambda pidx,val: list (coefD,i,j)."""
    base = ['c0', 'c1', 'c2', 'c3', 'e0', 'e1', 'e2', 'e3', 'd']
    if name == 'line':
        return dict(params=base + ['A', 'B', 'C'], m=1)

    if name == 'conic':
        return dict(params=base + ['a', 'b', 'cc', 'dd', 'ee', 'ff'], m=2)

    if name == 'cubic_general':
        return dict(params=base + ['g%d' % i for i in range(10)], m=3)

    if name.startswith('graph'):
        mm = int(name[5:])
        return dict(params=base + ['h%d' % i for i in range(mm + 1)], m=mm)

    if name.startswith('power'):
        nn = int(name[5:])
        return dict(params=base + ['a'], m=nn)

    raise ValueError(name)


def terms_as_d(name, val, tD, n):
    """Build the coefficient duals and (i,j) multi-indices of F for family `name`."""
    idx = {p: k for k, p in enumerate(FAM['params'])}
    N = len(FAM['params']) + 1  # +1 for t gradient slot
    ng = N

    def par(nm):
        return D(val[nm], [(1 if k == idx[nm] else 0) for k in range(N - 1)] + [0])

    if name == 'line':
        return [(par('A'), 1, 0), (par('B'), 0, 1), (-par('C'), 0, 0)]
    if name == 'conic':
        return [(par('a'), 2, 0), (par('b'), 1, 1), (par('cc'), 0, 2),
                (par('dd'), 1, 0), (par('ee'), 0, 1), (-par('ff'), 0, 0)]
    if name == 'cubic_general':
        out = []
        mon = [(3, 0), (2, 1), (1, 2), (0, 3), (2, 0), (1, 1), (0, 2), (1, 0), (0, 1), (0, 0)]
        for k, (i, j) in enumerate(mon):
            out.append((par('g%d' % k), i, j))
        return out
    if name.startswith('graph'):
        mm = int(name[5:])
        out = [(D(1, [0] * (N - 1) + [0]), 0, 1)]  # Y
        for k in range(mm + 1):
            out.append((-par('h%d' % k), k, 0))
        return out
    if name.startswith('power'):
        nn = int(name[5:])
        return [(D(1, [0] * (N - 1) + [0]), 0, 1), (-par('a'), nn, 0)]
    raise ValueError(name)


def Q_grad(name, val, tv, n):
    """Return D = Q(tv) with gradient wrt params (and t as last slot)."""
    N = len(FAM['params']) + 1
    m = FAM['m']
    idx = {p: k for k, p in enumerate(FAM['params'])}

    def par(nm):
        return D(val[nm], [(1 if k == idx[nm] else 0) for k in range(N - 1)] + [0])

    tD = D(tv, [0] * (N - 1) + [1])
    zero = Dzero(N)
    x = par('c0') + par('c1') * tD + par('c2') * tD ** 2 + par('c3') * tD ** 3
    y = par('e0') + par('e1') * tD + par('e2') * tD ** 2 + par('e3') * tD ** 3
    one = D(1, [0] * N)
    xp = par('c1') + 2 * par('c2') * tD + 3 * par('c3') * tD ** 2
    yp = par('e1') + 2 * par('e2') * tD + 3 * par('e3') * tD ** 2
    q = xp ** 2 + yp ** 2
    al = (-par('d') * yp, x)   # x w - d y'   = X w
    be = (par('d') * xp, y)    # y w + d x'   = Y w
    tot = (zero, zero)
    for (coef, i, j) in terms_as_d(name, val, tD, N):
        e = m - i - j
        term = rpow(al, i, q)
        tb = rpow(be, j, q)
        term = rmul(term, tb, q)
        wa, wb = wpow(e, q, N)
        term = (term[0] * wa + term[1] * wb * q, term[0] * wb + term[1] * wa)
        tot = (tot[0] + coef * term[0], tot[1] + coef * term[1])
    A, B = tot
    return A * A - B * B * q


def dims(name, seed=0, Npt=None, exact_rank=None):
    global FAM
    FAM = build_family(name)
    m = FAM['m']
    N = 10 * m
    npr = len(FAM['params'])
    random.seed(seed)
    val = {p: random.randint(1, P - 1) for p in FAM['params']}
    ts = random.sample(range(1, P), N + 1)
    Mplain = []
    Mfull = []
    for tv in ts:
        Q = Q_grad(name, val, tv, None)
        dqt = Q.g[-1]
        plain = Q.g[:-1]
        Mplain.append(plain)
        Mfull.append(plain + [dqt, tv * dqt % P, tv * tv % P * dqt % P])
    rp = gf_rank(Mplain)
    rf = gf_rank(Mfull)
    return rp, rf, m, N, npr


if __name__ == '__main__':
    tests = ['line', 'conic', 'cubic_general', 'graph2', 'graph3', 'graph4', 'graph6',
             'power7', 'power8', 'power9']
    print('family           m   N   npar  rank_plain  D  codimP  rank_full  Dsat  codimMob')
    for nm in tests:
        try:
            rp, rf, m, N, npr = dims(nm)
            dimP = rp - 1
            Dsat = rf - 1
            print('%-16s %2d %4d %5d %8d %5d %7d %10d %5d %9d'
                  % (nm, m, N, npr, rp, dimP, N - dimP, rf, Dsat, N - Dsat))
            sys.stdout.flush()
        except Exception as e:
            import traceback
            print(nm, 'ERROR', repr(e))
            traceback.print_exc()
            sys.stdout.flush()
