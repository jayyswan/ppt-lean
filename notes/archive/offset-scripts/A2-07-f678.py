"""A2-07: F6 (parabola offset), F8 (ellipse offset), F9 (reversed) dimensions via the general
engine in A2-06-dim2.py.  The base curve may be any rational parametrisation; rows count is
generous so the evaluation-rank equals the coefficient-Jacobian rank."""
import importlib.util
import random, sys
import sympy as sp
from sympy import symbols, diff, expand, Integer

spec = importlib.util.spec_from_file_location(
    'a206', r'C:\dev\Powerpoint\lean\archived files\offset-scripts\A2-06-dim2.py')
m206 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m206)
Fam = m206.Fam
D = m206.D
P = m206.P
T = m206.T


def dims(F, rows):
    F.prep()
    n = len(F.params) + 1
    random.seed(0)
    vals = {p: random.randint(1, P - 1) for p in F.params}
    ts = random.sample(range(1, P), rows)
    Mp, Mf = [], []
    for tv in ts:
        Q = F.Q(vals, tv)
        dq = Q.g[-1]
        Mp.append(Q.g[:-1])
        Mf.append(Q.g[:-1] + [dq, tv * dq % P, tv * tv % P * dq % P])
    return m206.gf_rank(Mp), m206.gf_rank(Mf), len(F.params)


def report(name, F, N, rows=60):
    try:
        rp, rf, npar = dims(F, rows)
        print('%-22s N=%3d npar=%2d rank=%2d D=%2d codimP=%3d Dsat=%2d' %
              (name, N, npar, rp, rp - 1, N - (rp - 1), rf - 1))
    except Exception as ex:
        import traceback
        print(name, 'ERR', ex)
        traceback.print_exc()
    sys.stdout.flush()


if __name__ == '__main__':
    X, Y = symbols('X Y')
    # ---- F6: base parabola, general quadratic pair (6 params) ----
    p0, p1, p2, q0, q1, q2, d = symbols('p0 p1 p2 q0 q1 q2 d')
    xp2 = p0 + p1 * T + p2 * T ** 2
    yp2 = q0 + q1 * T + q2 * T ** 2
    base = [p0, p1, p2, q0, q1, q2, d]
    A, B, C = symbols('A B C')
    aa, bb, cc, dd, ee, ff = symbols('aa bb cc dd ee ff')
    lam, u, v, sx, sy, tx, ty = symbols('lam u v sx sy tx ty')

    lineF = [(A, 1, 0), (B, 0, 1), (-C, 0, 0)]
    conicF = [(aa, 2, 0), (bb, 1, 1), (cc, 0, 2), (dd, 1, 0), (ee, 0, 1), (-ff, 0, 0)]
    Minv = sp.Matrix([[u, v], [-v, u]]) * sp.Matrix([[1 / sx, 0], [0, 1 / sy]])
    Xl = Minv[0, 0] * (X - tx) + Minv[0, 1] * (Y - ty)
    Yl = Minv[1, 0] * (X - tx) + Minv[1, 1] * (Y - ty)
    Fbe = expand(sp.numer(sp.together(Yl ** 2 - Xl ** 3 + lam * Xl ** 2)))
    bezF = [(expand(Fbe.coeff(X, i).coeff(Y, j)), i, j)
            for i in range(4) for j in range(4 - i) if Fbe.coeff(X, i).coeff(Y, j) != 0]

    report('F6 parabola x line', Fam('p_line', base + [A, B, C], xp2, yp2, d, 1, lineF), 6)
    report('F6 parabola x conic', Fam('p_conic', base + [aa, bb, cc, dd, ee, ff], xp2, yp2, d, 2, conicF), 12)
    report('F6 parabola x bezier', Fam('p_bez', base + [lam, u, v, sx, sy, tx, ty], xp2, yp2, d, 3, bezF), 18)

    # ---- F8: base ellipse, rational parametrisation (4 params + d) ----
    h, k, a, b, de = symbols('h k a b de')
    xe = h + a * (1 - T ** 2) / (1 + T ** 2)
    ye = k + 2 * b * T / (1 + T ** 2)
    ebase = [h, k, a, b, de]
    report('F8 ellipse x line', Fam('e_line', ebase + [A, B, C], xe, ye, de, 1, lineF), 8)
    report('F8 ellipse x conic', Fam('e_conic', ebase + [aa, bb, cc, dd, ee, ff], xe, ye, de, 2, conicF), 16)
    report('F8 ellipse x bezier', Fam('e_bez', ebase + [lam, u, v, sx, sy, tx, ty], xe, ye, de, 3, bezF), 24)
