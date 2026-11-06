"""A2-09: find an explicit F2 (offset cubic x conic) sample with 7+ real roots, print its
parameters, its real roots, and the genuine-crossing check.  Real-root counts come from
Sturm (sympy)."""
import random, sys
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
    return sp.expand(A ** 2 - B ** 2 * q)


def rat(rng, lo=-6, hi=6):
    return sp.Rational(rng.randint(lo, hi), rng.randint(1, 4))


def main():
    rng = random.Random(22)
    for i in range(400):
        c = [rat(rng) for _ in range(4)]
        e = [rat(rng) for _ in range(4)]
        x = c[0] + c[1] * t + c[2] * t ** 2 + c[3] * t ** 3
        y = e[0] + e[1] * t + e[2] * t ** 2 + e[3] * t ** 3
        d = rat(rng, 1, 5)
        # positive-definite quadratic part: a genuine (axis-aligned) ellipse
        al, be = rat(rng, 1, 5), rat(rng, 1, 5)
        h, k = rat(rng), rat(rng)
        F = al * (X - h) ** 2 + be * (Y - k) ** 2 - 1
        Q = build(x, y, d, F, 2)
        P = sp.Poly(Q, t)
        if P.degree() < 20:
            continue
        r = int(P.count_roots())
        if r >= 7:
            print('found real-root count', r, 'at sample', i)
            print('x =', x)
            print('y =', y)
            print('d =', d)
            print('F =', F)
            cff = [mp.mpf(int(sp.Rational(z).p)) / mp.mpf(int(sp.Rational(z).q)) for z in P.all_coeffs()]
            mp.mp.dps = 50
            rts = mp.polyroots(cff, maxsteps=400, extraprec=400)
            real = sorted([mp.re(z) for z in rts if abs(mp.im(z)) < mp.mpf('1e-35')])
            print('real roots:', [mp.nstr(z, 30) for z in real])
            fX = sp.lambdify(t, x, 'mpmath')
            fY = sp.lambdify(t, y, 'mpmath')
            fxp = sp.lambdify(t, sp.diff(x, t), 'mpmath')
            fyp = sp.lambdify(t, sp.diff(y, t), 'mpmath')
            Fn = sp.lambdify((X, Y), F, 'mpmath')
            for z in real:
                wv = mp.sqrt(fxp(z) ** 2 + fyp(z) ** 2)
                best = min(abs(Fn(fX(z) - s * d * fyp(z) / wv, fY(z) + s * d * fxp(z) / wv))
                           for s in (1, -1))
                print('   t=%s  min|F(offset)|=%s' % (mp.nstr(z, 20), mp.nstr(best, 4)))
            return
    print('none found')
    sys.stdout.flush()


if __name__ == '__main__':
    main()
