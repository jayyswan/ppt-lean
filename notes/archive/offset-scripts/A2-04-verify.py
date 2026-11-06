"""A2-04-verify: certify the conic instance.  Print integer Q, check irreducibility over Q,
check every real root is a genuine crossing for one sign of d, give 40-digit roots."""
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
    return sp.expand(A ** 2 - B ** 2 * q), q


def real_roots(QI, dps=60):
    cf = [sp.Rational(c) for c in QI.all_coeffs()]
    mp.mp.dps = dps
    cff = [mp.mpf(int(c.p)) / mp.mpf(int(c.q)) for c in cf]
    roots = mp.polyroots(cff, maxsteps=300, extraprec=300)
    return sorted([mp.re(r) for r in roots if abs(mp.im(r)) < mp.mpf('1e-40')])


if __name__ == '__main__':
    x = t ** 3 + t + 1
    y = 2 * t ** 3 - t ** 2 + 3
    d = sp.Integer(2)
    X, Y = sp.symbols('X Y')
    F = 4 * X ** 2 + 9 * Y ** 2 - 36
    Q, q = build(x, y, d, F, 2)
    QI = sp.Poly(Q, t).clear_denoms()[1]
    print('content:', sp.gcd(list(QI.all_coeffs())))
    print('irreducible over Q:', QI.is_irreducible)
    print('degree:', QI.degree())
    print('Q2 =', QI.as_expr())
    print()
    rr = real_roots(QI)
    print('real roots (40 digits):')
    for r in rr:
        print('  ', mp.nstr(r, 40))
    fX = sp.lambdify(t, x, 'mpmath')
    fY = sp.lambdify(t, y, 'mpmath')
    fxp = sp.lambdify(t, sp.diff(x, t), 'mpmath')
    fyp = sp.lambdify(t, sp.diff(y, t), 'mpmath')
    Fn = sp.lambdify((X, Y), F, 'mpmath')
    print('genuine-crossing check (should be ~0 for exactly one sign):')
    for r in rr:
        wv = mp.sqrt(fxp(r) ** 2 + fyp(r) ** 2)
        row = []
        for sgn in (1, -1):
            Xv = fX(r) - sgn * d * fyp(r) / wv
            Yv = fY(r) + sgn * d * fxp(r) / wv
            row.append(mp.nstr(Fn(Xv, Yv), 6))
        print('  t=%s  F(d)=%s  F(-d)=%s' % (mp.nstr(r, 18), row[0], row[1]))
