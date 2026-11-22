# Session 9: exact critical-point certificate that g6 >= 0 on real trace-zero vectors.
# g6 = 231 p2^3 - 966 p2 p4 + 1008 p6 - 256 p3^2.
# Lagrange: at a critical point of g6 on {p1=0, p2=1}, every coordinate is a root of
#   Q(x) = 6048 x^5 - 3864 p2 x^3 - 1536 p3 x^2 + c1 x + c0   (c1, c0 absorb multipliers),
# so a critical point has k <= 5 distinct values v_1..v_k (multiplicities m), and
# Prod(x - v_i) * R(x) must have x^4, x^3, x^2 coefficients 0, -23/36 p2, -16/63 p3.
import itertools, random, re
import sympy as sp
import mpmath as mp
mp.mp.dps = 60
x = sp.Symbol('x')

def partitions(n, k, maxpart=None):
    if maxpart is None: maxpart = n
    if k == 0:
        if n == 0: yield ()
        return
    for first in range(min(n - (k - 1), maxpart), 0, -1):
        for rest in partitions(n - first, k - 1, first):
            yield (first,) + rest

def g6_of(m, v):
    p = lambda j: sum(mi * vi**j for mi, vi in zip(m, v))
    return 231*p(2)**3 - 966*p(2)*p(4) + 1008*p(6) - 256*p(3)**2, p(2)

def system(m):
    k = len(m)
    v = sp.symbols('v1:%d' % (k + 1))
    P2 = sum(mi*vi**2 for mi, vi in zip(m, v)); P3 = sum(mi*vi**3 for mi, vi in zip(m, v))
    r = sp.symbols('r1:%d' % (6 - k)) if k < 5 else ()
    R = x**(5 - k) + sum(ri * x**(4 - k - i) for i, ri in enumerate(r))
    prod = sp.expand(sp.prod([x - vi for vi in v]) * R)
    target = {4: 0, 3: -sp.Rational(23, 36)*P2, 2: -sp.Rational(16, 63)*P3}
    eqs = [sp.expand(prod.coeff(x, d) - target[d]) for d in (4, 3, 2)]
    # eliminate r (triangular, linear)
    sol = {}
    for i, ri in enumerate(r):
        e = eqs[i].subs(sol)
        sol[ri] = sp.solve(e, ri)[0]
    rest = [sp.expand(e.subs(sol)) for e in eqs[len(r):]]
    lin = [sum(mi*vi for mi, vi in zip(m, v))]
    return v, lin, rest


import cypari
pari = cypari.pari
pari.set_real_precision(80)

def topari(e, names):
    s = str(sp.expand(e)).replace('**', '^')
    for old, new in names.items():
        s = re.sub(r'\b%s\b' % old, new, s)
    return pari(s)

def realroots(pol):
    # exact real-root isolation (polrootsreal) on the squarefree part
    pol = pari.substpol(pol, pari('a'), pari('a')) if False else pol
    if pari.poldegree(pol) <= 0: return []
    sf = pari('(f)->f/gcd(f,deriv(f))')(pol)
    return [rt for rt in pari.polrootsreal(sf)]

def solve_pattern(m, seed):
    k = len(m)
    v, lin, rest = system(m)
    rnd = random.Random(seed)
    dehom = sum(sp.Integer(rnd.randint(1, 97)) * vi for vi in v) - 1
    linear = [l for l in lin + rest if sp.Poly(l, *v).total_degree() == 1] + [dehom]
    nonlin = [e for e in rest if sp.Poly(e, *v).total_degree() > 1]
    s = sp.solve(linear, list(v), dict=True)[0]
    free = [vi for vi in v if vi not in s]
    assert len(free) == len(nonlin), (m, free, nonlin)
    eqs = [sp.expand(sp.numer(sp.together(e.subs(s)))) for e in nonlin]
    if any(e == 0 for e in eqs):
        return None, 'positive-dimensional (an equation vanishes identically)'
    names = {str(f): n for f, n in zip(free, ['a', 'b'])}
    pts = []
    if len(free) == 0:
        pts.append({})
    elif len(free) == 1:
        (u,) = free
        for rt in realroots(topari(eqs[0], names)):
            pts.append({u: rt})
    else:
        u, w = free
        A, B = topari(eqs[0], names), topari(eqs[1], names)
        res = pari.polresultant(A, B, pari('b'))
        if res == 0:
            return None, 'positive-dimensional (resultant 0)'
        for rt in realroots(res):
            Ab = pari.substpol(A, pari('a'), rt) if False else pari.subst(A, pari('a'), rt)
            Bb = pari.subst(B, pari('a'), rt)
            for w0 in pari.polroots(Ab):
                if abs(pari.imag(w0)) > 1e-50: continue
                w0r = pari.real(w0)
                if abs(pari.subst(Bb, pari('b'), w0r)) < 1e-40 * (1 + abs(pari.subst(Bb, pari('b'), 0))):
                    pts.append({u: rt, w: w0r})
    out = []
    for pt in pts:
        vals = []
        for vi in v:
            if vi in pt:
                vals.append(mp.mpf(str(pt[vi])))
            else:
                expr = s[vi]
                val = topari(expr, names)
                for f, n in names.items():
                    sym = [ff for ff in free if str(ff) == f][0]
                    val = pari.subst(val, pari(n), pt[sym])
                vals.append(mp.mpf(str(val)))
        G, p2 = g6_of(m, vals)
        if p2 == 0: continue
        out.append((G / p2**3, vals))
    return out, 'ok'

if __name__ == '__main__':
    overall = mp.inf
    zeros = []
    for k in range(2, 6):
        for m in partitions(9, k):
            out, status = solve_pattern(m, seed=hash(m) % 1000)
            if status != 'ok':
                print(m, status); continue
            mn = min((o[0] for o in out), default=None)
            print(m, 'critical pts:', len(out), 'min g6/p2^3 =', mp.nstr(mn, 15) if mn is not None else '-')
            for val, vals in out:
                overall = min(overall, val)
                distinct = []
                for t, mi in zip(vals, m):
                    for d in distinct:
                        if abs(d[0]-t) < mp.mpf('1e-15'): d[1] += mi; break
                    else: distinct.append([t, mi])
                mult = sorted(d[1] for d in distinct)
                if abs(val) < mp.mpf('1e-12'):
                    zeros.append((m, mult))
                    assert max(mult) >= 7, ('ZERO OFF THE PLANES', m, vals)
    print('overall min', mp.nstr(overall, 20))
    print('zero critical points (pattern, values):')
    for z in zeros: print(' ', z)
