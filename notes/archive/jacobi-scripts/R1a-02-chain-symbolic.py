# R1a step 1: verify the depth-3 offset/affine chain formula (F3).
# Method: sympy SYMBOLIC differentiation (exact), no nested mp.diff.
#
# Geometry (matching ppc/Pptc/Defs.lean):
#   unitNormal(g, t) = J g'(t) / |g'(t)|,  J(x,y) = (-y, x)
#   offsetParam(g, d) = g + d * unitNormal(g)
# One offset step, for a curve with velocity v = g':
#   d/dt offsetParam(g,d) = (1 - d*K/Q^{3/2}) v ,  K = det(v,v') , Q = |v|^2   (A)
# Consequence for the chain  A_n o off_{d_{n-1}} o ... o A_1 o off_{d_0}:
#   final velocity = S_n * A_(n) v,
#   S_n = 1 - sum_{k=0}^{n-1} d_k * det(A_(k)) * K / q_k^{3/2},
#   A_(k) = A_k...A_1 (A_(0)=I), q_k = |A_(k) v|^2.                            (F3)
import sympy as sp

t = sp.symbols("t", real=True)


def part_A():
    print("== Part A: symbolic one-step identity (A), generic curve ==")
    vx = sp.Function("vx")(t)
    vy = sp.Function("vy")(t)
    Q = vx**2 + vy**2
    n = sp.Matrix([-vy, vx]) / sp.sqrt(Q)
    dn = sp.Matrix([sp.diff(n[0], t), sp.diff(n[1], t)])
    K = vx * sp.diff(vy, t) - vy * sp.diff(vx, t)
    claim = sp.Matrix([-K / Q ** sp.Rational(3, 2) * vx,
                       -K / Q ** sp.Rational(3, 2) * vy])
    diff = sp.simplify(dn - claim)
    print("  n' + (K/Q^(3/2)) v =", diff.T)
    ok = sp.simplify(diff[0]) == 0 and sp.simplify(diff[1]) == 0
    print("  RESULT:", "PASS" if ok else "FAIL")
    return ok


def matmul(*ms):
    out = ms[0]
    for m in ms[1:]:
        out = out * m
    return out


def normal(g):
    gx, gy = g[0], g[1]
    v = sp.Matrix([sp.diff(gx, t), sp.diff(gy, t)])
    Q = v[0] ** 2 + v[1] ** 2
    return sp.Matrix([-v[1], v[0]]) / sp.sqrt(Q)


def offset(g, d):
    return g + d * normal(g)


def part_B(b=sp.Rational(7, 5), mats=None, ds=None):
    print("== Part B: depth-3 exact chain (rational data), symbolic t ==")
    if mats is None:
        mats = [sp.Matrix([[sp.Rational(3, 2), sp.Rational(1, 3)],
                           [sp.Rational(-2, 5), sp.Rational(5, 4)]]),
                sp.Matrix([[sp.Rational(1, 2), sp.Rational(-4, 3)],
                           [sp.Rational(2, 7), sp.Rational(9, 8)]]),
                sp.Matrix([[sp.Rational(5, 3), sp.Rational(2, 5)],
                           [sp.Rational(-1, 2), sp.Rational(7, 6)]])]
    if ds is None:
        ds = [sp.Rational(2, 5), sp.Rational(-3, 7), sp.Rational(4, 9)]
    A1, A2, A3 = mats
    d0, d1, d2 = ds

    P = sp.Matrix([sp.cos(t), b * sp.sin(t)])
    v = sp.Matrix([sp.diff(P[0], t), sp.diff(P[1], t)])
    vp = sp.Matrix([sp.diff(P[0], t, 2), sp.diff(P[1], t, 2)])
    K = sp.expand(v[0] * vp[1] - v[1] * vp[0])
    print("  base velocity v =", v.T, " K = det(v,v') =", sp.simplify(K))

    C0 = P
    C1 = A1 * offset(C0, d0)
    C2 = A2 * offset(C1, d1)
    C3 = A3 * offset(C2, d2)
    V3 = sp.Matrix([sp.diff(C3[0], t), sp.diff(C3[1], t)])

    I = sp.eye(2)
    As = [I, A1, matmul(A2, A1), matmul(A3, A2, A1)]
    ann = [I, A1, A2 * A1, A3 * A2 * A1]
    S = sp.Integer(1)
    for k in range(3):
        Ak = ann[k]
        Av = Ak * v
        qk = sp.expand(Av[0] ** 2 + Av[1] ** 2)
        detAk = sp.expand(Ak.det())
        S = S - ds[k] * detAk * K / qk ** sp.Rational(3, 2)
    S = sp.simplify(S)
    print("  predicted S_3 =", S)

    pred = sp.expand(S * (A3 * A2 * A1) * v)
    diff = V3 - pred
    print("  diff[0] =", sp.simplify(diff[0]))
    print("  diff[1] =", sp.simplify(diff[1]))
    ok = sp.simplify(diff[0]) == 0 and sp.simplify(diff[1]) == 0
    print("  RESULT:", "PASS" if ok else "FAIL")
    return ok


if __name__ == "__main__":
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    if mode in ("all", "A"):
        okA = part_A()
    else:
        okA = True
    if mode in ("all", "B"):
        okB = part_B()
    else:
        okB = True
    print("OVERALL:", "PASS" if (okA and okB) else "FAIL")
