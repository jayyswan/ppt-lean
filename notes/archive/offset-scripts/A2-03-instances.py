"""A2-03-instances: explicit crossing polynomials for conic and nodal-cubic second curves.

For numeric (rational) base cubic pair and second curve we build Q(t) exactly, report its
degree, factorisation mod primes (Chebotarev / irreducibility evidence), and its real roots
to high precision with mpmath.  Every real root of Q is a genuine crossing for one sign of d
(O4) hence lies in K by offsetCubicPair_cross_root_Pconstructible.
"""
import sympy as sp
import mpmath as mp

t, w = sp.symbols('t w')


def build(x, y, d, F, m):
    xp, yp = sp.diff(x, t), sp.diff(y, t)
    q = sp.expand(xp ** 2 + yp ** 2)
    Xs = x - d * yp / w
    Ys = y + d * xp / w
    Fs = sp.expand(F.subs({'X': Xs, 'Y': Ys}))
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
    Q = sp.expand(A ** 2 - B ** 2 * q)
    return sp.Poly(Q, t), q, (A, B)


def report(name, Q, primes=(1000003, 2000003, 3000017)):
    print('===', name, '===')
    print('degree:', Q.degree())
    lc = Q.LC()
    print('leading coeff:', lc)
    _, Qp = Q.clear_denoms()
    for p in primes:
        try:
            fl = sp.factor_list(Qp, modulus=p)[1]
            pat = sorted([f[0].degree() for f in fl], reverse=True)
            print('  mod %d factorization pattern:' % p, pat)
        except Exception as e:
            print('  mod', p, 'error', e)


def real_roots(Q, dps=40):
    coeffs = [sp.Rational(c) for c in Q.all_coeffs()]
    mp.mp.dps = dps
    cf = [mp.mpf(int(c.p)) / mp.mpf(int(c.q)) for c in coeffs]
    roots = mp.polyroots(cf, maxsteps=200, extraprec=200)
    out = []
    for r in roots:
        if abs(mp.im(r)) < mp.mpf('1e-25'):
            out.append(mp.re(r))
    return sorted(out)


if __name__ == '__main__':
    # base cubic pair
    x = t ** 3 + t + 1
    y = 2 * t ** 3 - t ** 2 + 3
    d = sp.Integer(2)
    X, Y = sp.symbols('X Y')

    # ---- F2: ellipse X^2/9 + Y^2/4 = 1  ->  4X^2+9Y^2-36 ----
    F2 = 4 * X ** 2 + 9 * Y ** 2 - 36
    Q2, q2, AB2 = build(x, y, d, F2, 2)
    report('F2 conic 4X^2+9Y^2=36', Q2)
    rr2 = real_roots(Q2)
    print('real roots:', [mp.nstr(r, 30) for r in rr2])

    # ---- F3: nodal cubic Y^2 = X^3 - lam X^2, lam=1 ----
    lam = sp.Integer(1)
    F3 = Y ** 2 - X ** 3 + lam * X ** 2
    Q3, q3, AB3 = build(x, y, d, F3, 3)
    report('F3 nodal cubic Y^2=X^3-X^2', Q3)
    rr3 = real_roots(Q3)
    print('real roots:', [mp.nstr(r, 30) for r in rr3])
