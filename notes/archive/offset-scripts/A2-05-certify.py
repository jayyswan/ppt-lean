"""A2-05: clean certification of the F2 (ellipse) and F3 (nodal cubic) instances.

For each: build the rationalised crossing polynomial Q, clear denominators, test
irreducibility over Q, list real roots to 40 digits, and verify each real root is a genuine
crossing for exactly one sign of d (F(offset)=0).  Also print factorisation patterns mod
several large primes (Chebotarev cycle-type evidence).
"""
import sympy as sp
import mpmath as mp

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
    return sp.Poly(sp.expand(A ** 2 - B ** 2 * q), t), q


def roots(QI, dps=60):
    mp.mp.dps = dps
    cc = [mp.mpf(int(sp.Rational(c).p)) / mp.mpf(int(sp.Rational(c).q)) for c in QI.all_coeffs()]
    r = mp.polyroots(cc, maxsteps=500, extraprec=500)
    return sorted([mp.re(z) for z in r if abs(mp.im(z)) < mp.mpf('1e-40')])


def check(name, x, y, d, F, m, primes=(1000003, 2000003, 3000017, 4000037)):
    Q, q = build(x, y, d, F, m)
    QI = sp.Poly(Q, t).clear_denoms()[1]
    print('===', name, '===')
    print('degree', QI.degree(), ' content', sp.gcd(list(QI.all_coeffs())),
          ' irreducible over Q:', QI.is_irreducible)
    for p in primes:
        fl = sp.factor_list(QI, modulus=p)[1]
        print('   mod %d pattern:' % p, sorted([f[0].degree() for f in fl], reverse=True))
    rr = roots(QI)
    print('   real roots:', [mp.nstr(z, 40) for z in rr])
    fX = sp.lambdify(t, x, 'mpmath')
    fY = sp.lambdify(t, y, 'mpmath')
    fxp = sp.lambdify(t, sp.diff(x, t), 'mpmath')
    fyp = sp.lambdify(t, sp.diff(y, t), 'mpmath')
    Fn = sp.lambdify((X, Y), F, 'mpmath')
    for z in rr:
        wv = mp.sqrt(fxp(z) ** 2 + fyp(z) ** 2)
        v = []
        for s in (1, -1):
            Xv = fX(z) - s * d * fyp(z) / wv
            Yv = fY(z) + s * d * fxp(z) / wv
            v.append(mp.nstr(Fn(Xv, Yv), 4))
        print('   t=%s  F(+d)=%s  F(-d)=%s' % (mp.nstr(z, 22), v[0], v[1]))
    print()
    return QI


if __name__ == '__main__':
    x = t ** 3 + t + 1
    y = 2 * t ** 3 - t ** 2 + 3
    d = sp.Integer(2)
    check('F2: offset cubic x ellipse 4X^2+9Y^2=36', x, y, d, 4 * X ** 2 + 9 * Y ** 2 - 36, 2)
    check('F3: offset cubic x nodal cubic Y^2=X^3-X^2', x, y, d,
          Y ** 2 - X ** 3 + X ** 2, 3)
