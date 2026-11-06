# R1a step 1b: verify the depth-3 chain formula with truncated Taylor (jet) arithmetic.
# This is exact (to working precision), fast, and uses NO nested finite differences:
# a "jet" is the Taylor expansion of a function of t up to order m, and all operations
# (+, -, *, /, sqrt, sin, cos) are the corresponding series operations. Feeding t = t0 + eps
# through the composite chain returns every derivative up to order m, in particular the
# true velocity of the chain at t0, to full mpmath precision.
import sys

import mpmath as mp

mp.mp.dps = 30
M = 14  # truncation order

zero = mp.mpf(0)


def jconst(c):
    return [mp.mpf(c)] + [zero] * M


def jadd(a, b):
    return [a[i] + b[i] for i in range(M + 1)]


def jsub(a, b):
    return [a[i] - b[i] for i in range(M + 1)]


def jneg(a):
    return [-x for x in a]


def jscale(c, a):
    return [mp.mpf(c) * a[i] for i in range(M + 1)]


def jmul(a, b):
    c = [zero] * (M + 1)
    for k in range(M + 1):
        s = zero
        for i in range(k + 1):
            s += a[i] * b[k - i]
        c[k] = s
    return c


def jrecip(a):
    c = [zero] * (M + 1)
    c[0] = 1 / a[0]
    for k in range(1, M + 1):
        s = zero
        for i in range(1, k + 1):
            s += a[i] * c[k - i]
        c[k] = -s / a[0]
    return c


def jdiv(a, b):
    return jmul(a, jrecip(b))


def jsqrt(a):
    c = [zero] * (M + 1)
    c[0] = mp.sqrt(a[0])
    for k in range(1, M + 1):
        s = zero
        for i in range(1, k):
            s += c[i] * c[k - i]
        c[k] = (a[k] - s) / (2 * c[0])
    return c


def jderiv(a):
    return [(k + 1) * a[k + 1] for k in range(M)] + [zero]


def _pow(h, n):
    r = jconst(1)
    for _ in range(n):
        r = jmul(r, h)
    return r


def jsin(a):
    a0 = a[0]
    h = [zero] + a[1:]
    cosh = jconst(0)
    sinh = jconst(0)
    fact = mp.mpf(1)
    for k in range(0, M + 1, 2):
        if k > 0:
            fact *= k * (k - 1)
        cosh = jadd(cosh, jscale((-1) ** (k // 2) / fact, _pow(h, k)))
    fact = mp.mpf(1)
    for k in range(1, M + 1, 2):
        fact *= k * (k - 1) if k > 1 else 1
        sinh = jadd(sinh, jscale((-1) ** ((k - 1) // 2) / fact, _pow(h, k)))
    return jadd(jscale(mp.sin(a0), cosh), jscale(mp.cos(a0), sinh))


def jcos(a):
    a0 = a[0]
    h = [zero] + a[1:]
    cosh = jconst(0)
    sinh = jconst(0)
    fact = mp.mpf(1)
    for k in range(0, M + 1, 2):
        if k > 0:
            fact *= k * (k - 1)
        cosh = jadd(cosh, jscale((-1) ** (k // 2) / fact, _pow(h, k)))
    fact = mp.mpf(1)
    for k in range(1, M + 1, 2):
        fact *= k * (k - 1) if k > 1 else 1
        sinh = jadd(sinh, jscale((-1) ** ((k - 1) // 2) / fact, _pow(h, k)))
    return jsub(jscale(mp.cos(a0), cosh), jscale(mp.sin(a0), sinh))


def tjet(t0):
    return [t0, mp.mpf(1)] + [zero] * (M - 1)


# curve = pair of jets; velocity = pair of jets (derivative)
def vel(c):
    return (jderiv(c[0]), jderiv(c[1]))


def normal(c):
    vx, vy = vel(c)
    Q = jadd(jmul(vx, vx), jmul(vy, vy))
    sp = jsqrt(Q)
    return (jdiv(jneg(vy), sp), jdiv(vx, sp))


def offset(c, d):
    nx, ny = normal(c)
    return (jadd(c[0], jscale(d, nx)), jadd(c[1], jscale(d, ny)))


def lin(A, c):
    return (jadd(jscale(A[0][0], c[0]), jscale(A[0][1], c[1])),
            jadd(jscale(A[1][0], c[0]), jscale(A[1][1], c[1])))


def matmul(*ms):
    out = ms[0]
    for B in ms[1:]:
        out = tuple(tuple(sum(out[i][k] * B[k][j] for k in range(2)) for j in range(2))
                    for i in range(2))
    return out


def mm(A, v):
    return (A[0][0] * v[0] + A[0][1] * v[1], A[1][0] * v[0] + A[1][1] * v[1])


def det2(A):
    return A[0][0] * A[1][1] - A[0][1] * A[1][0]


def vnorm(v):
    return mp.sqrt(v[0] ** 2 + v[1] ** 2)


def run(b, t0, mats, ds, tag):
    A1, A2, A3 = mats
    d0, d1, d2 = ds
    T = tjet(t0)
    P = (jcos(T), jscale(b, jsin(T)))
    C1 = lin(A1, offset(P, d0))
    C2 = lin(A2, offset(C1, d1))
    C3 = lin(A3, offset(C2, d2))
    actual = (C3[0][1], C3[1][1])  # order-1 coefficients = true velocity

    v = (-mp.sin(t0), b * mp.cos(t0))
    K = mp.mpf(b)
    As = [((mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1))), A1, matmul(A2, A1),
          matmul(A3, A2, A1)]
    qs = [mm(As[k], v) for k in range(4)]
    q = [qk[0] ** 2 + qk[1] ** 2 for qk in qs]
    dets = [det2(As[k]) for k in range(3)]
    ds_ = [d0, d1, d2]
    # sign-corrected recurrence (using exact sign of running S)
    S = mp.mpf(1)
    for k in range(3):
        S = S - ds_[k] * (1 if S >= 0 else -1) * dets[k] * K / q[k] ** mp.mpf("1.5")
    pred = (S * qs[3][0], S * qs[3][1])
    # naive additive formula (overview F3, no sign)
    S_naive = mp.mpf(1)
    for k in range(3):
        S_naive = S_naive - ds_[k] * dets[k] * K / q[k] ** mp.mpf("1.5")
    pred_naive = (S_naive * qs[3][0], S_naive * qs[3][1])

    ec = vnorm((actual[0] - pred[0], actual[1] - pred[1]))
    en = vnorm((actual[0] - pred_naive[0], actual[1] - pred_naive[1]))
    print(f"[{tag}] S={mp.nstr(S, 12)}  |actual|= {mp.nstr(vnorm(actual),12)}")
    print(f"    err sign-corrected = {mp.nstr(ec, 6)}")
    print(f"    err naive (F3 sum)  = {mp.nstr(en, 6)}")
    return ec, en, S


if __name__ == "__main__":
    # generic (S stays positive) random-ish data
    A1 = ((mp.mpf("1.5"), mp.mpf("0.333")), (mp.mpf("-0.4"), mp.mpf("1.25")))
    A2 = ((mp.mpf("0.5"), mp.mpf("-1.333")), (mp.mpf("0.2857"), mp.mpf("1.125")))
    A3 = ((mp.mpf("1.6667"), mp.mpf("0.4")), (mp.mpf("-0.5"), mp.mpf("1.1667")))
    e1 = run(mp.mpf("1.7"), mp.mpf("1.0"), [A1, A2, A3],
             [mp.mpf("0.4"), mp.mpf("-0.42"), mp.mpf("0.44")], "generic S>0")
    # force a sign flip: d0 large so S1<0
    e2 = run(mp.mpf("1.7"), mp.mpf("1.0"), [A1, A2, A3],
             [mp.mpf("1.5"), mp.mpf("-0.42"), mp.mpf("0.44")], "sign-flip S1<0")
    print("PASS generic" if e1[0] < mp.mpf("1e-25") else "FAIL generic")
    print("PASS signflip" if e2[0] < mp.mpf("1e-25") else "FAIL signflip")
    print("NOTE naive error grows when S crosses 0:", mp.nstr(e2[1], 4))
