"""A2-01: general rationalization of F(gamma(t)+d n(t)/w) and Jacobian dimension.

Framework
---------
Base curve: cubic pair gamma(t) = (x(t), y(t)), cubics with coefficients c0..c3, e0..e3.
w = sqrt(x'^2+y'^2), q = x'^2+y'^2 (quartic). Offset point:
    Gamma(t) = (x - d*y'/w, y + d*x'/w).
Second curve given implicitly by F(X,Y)=0 of degree m.
Multiply by w^m, expand, reduce mod (w^2 - q):  w^m F(Gamma) = A(t) + B(t) w.
Crossing polynomial:  Q(t) = A^2 - B^2 q   (roots = genuine crossings for sign +/- d, O4).

Degree of Q is 10m generically (checked).
"""
import sympy as sp
from sympy import Rational as R
import random, sys

t, w, d = sp.symbols('t w d')
X, Y = sp.symbols('X Y')

c = sp.symbols('c0:4')
e = sp.symbols('e0:4')
x = c[0] + c[1] * t + c[2] * t ** 2 + c[3] * t ** 3
y = e[0] + e[1] * t + e[2] * t ** 2 + e[3] * t ** 3
xp = sp.diff(x, t)
yp = sp.diff(y, t)
q = sp.expand(xp ** 2 + yp ** 2)


def reduce_w(expr):
    """Reduce a polynomial in w with coefficients in Q(t,...) modulo w^2-q."""
    expr = sp.expand(expr)
    p = sp.Poly(expr, w)
    deg = p.degree()
    A = sp.Integer(0)
    B = sp.Integer(0)
    for k in range(deg, -1, -1):
        ck = p.coeff_monomial(w ** k)
        if ck == 0:
            continue
        if k % 2 == 0:
            A += ck * q ** (k // 2)
        else:
            B += ck * q ** ((k - 1) // 2)
    return sp.expand(A), sp.expand(B)


def crosspoly(F, m):
    """Return Q(t) = A^2 - B^2 q for implicit F of degree m."""
    Fx = F.subs({X: x - d * yp / w, Y: y + d * xp / w})
    expr = sp.expand(w ** m * Fx)
    A, B = reduce_w(expr)
    return sp.expand(A ** 2 - B ** 2 * q)


def coeff_list(Q, N):
    p = sp.Poly(Q, t)
    return [sp.expand(p.coeff_monomial(t ** i)) for i in range(N + 1)]


def rank_from_Q(Q, N, params, vals, prime):
    """Rank of d(coefficients)/d(params) at vals, mod prime."""
    cl = coeff_list(Q, N)
    rows = []
    for i in range(N + 1):
        ci = cl[i]
        row = []
        for pj in params:
            dij = sp.expand(sp.diff(ci, pj)).subs(vals)
            row.append(int(sp.numer(dij)) * pow(int(sp.denom(dij)), -1, prime) % prime)
        rows.append(row)
    return gf_rank(rows, prime)


def gf_rank(rows, prime):
    M = [r[:] for r in rows]
    ncol = len(M[0]) if M else 0
    rank = 0
    for col in range(ncol):
        piv = None
        for i in range(rank, len(M)):
            if M[i][col] % prime != 0:
                piv = i
                break
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        inv = pow(M[rank][col] % prime, -1, prime)
        M[rank] = [(v * inv) % prime for v in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col] % prime != 0:
                f = M[i][col] % prime
                M[i] = [(M[i][k] - f * M[rank][k]) % prime for k in range(ncol)]
        rank += 1
        if rank == len(M):
            break
    return rank


def rand_vals(params, seed):
    random.seed(seed)
    return {p: R(random.randint(-9, 9), random.randint(1, 5)) for p in params}


if __name__ == '__main__':
    P = 2 ** 61 - 1
    # ---- F1: line ----
    A_, B_, C_ = sp.symbols('A B C')
    F1 = A_ * X + B_ * Y - C_
    Q1 = crosspoly(F1, 1)
    print('F1 degree in t:', sp.Poly(Q1, t).degree())
    # match normal form
    u = A_ * x + B_ * y - C_
    v = B_ * x - A_ * y
    vp = sp.diff(v, t)
    up = sp.diff(u, t)
    norm = sp.expand((u ** 2 * (up ** 2 + vp ** 2) - d ** 2 * (A_ ** 2 + B_ ** 2) * vp ** 2) / (A_ ** 2 + B_ ** 2))
    print('F1 equals normal form (sign):', sp.simplify(Q1 + norm) == 0)
    print('F1 equals -normal form:', sp.simplify(Q1 - norm) == 0)

    # ---- General degree check for conic and cubic ----
    a_, b_, cc_, dd_, ee_, ff_ = sp.symbols('a b cc dd ee ff')
    F2 = a_ * X ** 2 + b_ * X * Y + cc_ * Y ** 2 + dd_ * X + ee_ * Y + ff_
    Q2 = crosspoly(F2, 2)
    print('F2 degree in t (should be 20):', sp.Poly(Q2, t).degree())

    g = sp.symbols('g0:10')
    F3 = sum(g[i] * X ** (i // 4) * Y ** (i % 4) for i in range(10))  # placeholder, replaced below
    F3 = (g[0] * X ** 3 + g[1] * X ** 2 * Y + g[2] * X * Y ** 2 + g[3] * Y ** 3
          + g[4] * X ** 2 + g[5] * X * Y + g[6] * Y ** 2 + g[7] * X + g[8] * Y + g[9])
    Q3 = crosspoly(F3, 3)
    print('F3 degree in t (should be 30):', sp.Poly(Q3, t).degree())

    # ---- F3 dimension, general cubic ----
    params3 = list(c) + list(e) + [d] + list(g)
    vals3 = rand_vals(params3, 1)
    r3 = rank_from_Q(Q3, 30, params3, vals3, P)
    print('F3 rank (general cubic), params=', len(params3), 'rank=', r3, 'D=', r3 - 1)

    # ---- F2 dimension, conic ----
    params2 = list(c) + list(e) + [d] + [a_, b_, cc_, dd_, ee_, ff_]
    vals2 = rand_vals(params2, 2)
    r2 = rank_from_Q(Q2, 20, params2, vals2, P)
    print('F2 rank (general conic), params=', len(params2), 'rank=', r2, 'D=', r2 - 1)

    # ---- F1 dimension, line ----
    params1 = list(c) + list(e) + [d, A_, B_, C_]
    vals1 = rand_vals(params1, 3)
    r1 = rank_from_Q(Q1, 10, params1, vals1, P)
    print('F1 rank (line), params=', len(params1), 'rank=', r1, 'D=', r1 - 1)
