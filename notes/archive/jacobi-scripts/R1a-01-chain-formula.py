# R1a step 1: verify the offset/affine chain formula (F3) of PLAN-jacobi-00-overview.
# Claim (signed speed): for chain  A_n o off_{d_{n-1}} o ... o A_1 o off_{d_0}
# acting on base curve with velocity v,
#   final velocity vector = Psi_n * A_(n) v,   Psi_n = 1 - sum_{k=0}^{n-1} d_k det(A_(k)) * K / Q_k^{3/2},
# where A_(k) = A_k...A_1 (A_(0)=I), Q_k = |A_(k) v|^2, K = det(v, v').
# We check it as a VECTOR identity at a depth-3 chain with mpmath numeric derivatives.
import random

import mpmath as mp

mp.mp.dps = 40
_rng = random.Random()


def vsub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def vadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def smul(s, a):
    return (s * a[0], s * a[1])


def norm(a):
    return mp.sqrt(a[0] ** 2 + a[1] ** 2)


def det(a, b):
    return a[0] * b[1] - a[1] * b[0]


def normal(P, t):
    px = mp.diff(lambda s: P(s)[0], t)
    py = mp.diff(lambda s: P(s)[1], t)
    n = mp.sqrt(px ** 2 + py ** 2)
    return (-py / n, px / n)


def offset(P, d):
    return lambda t: vadd(P(t), smul(d, normal(P, t)))


def lin(A, P):
    return lambda t: (A[0][0] * P(t)[0] + A[0][1] * P(t)[1],
                      A[1][0] * P(t)[0] + A[1][1] * P(t)[1])


def matmul(A, B):
    return ((A[0][0] * B[0][0] + A[0][1] * B[1][0], A[0][0] * B[0][1] + A[0][1] * B[1][1]),
            (A[1][0] * B[0][0] + A[1][1] * B[1][0], A[1][0] * B[0][1] + A[1][1] * B[1][1]))


def rand_GL2():
    th = mp.mpf(str(_rng.random())) * mp.pi
    s1 = mp.mpf("0.3") + mp.mpf(str(_rng.random())) * mp.mpf("2.0")
    s2 = mp.mpf("0.3") + mp.mpf(str(_rng.random())) * mp.mpf("2.0")
    c, s = mp.cos(th), mp.sin(th)
    R = ((c, -s), (s, c))
    S = ((s1, 0), (0, s2))
    return matmul(R, S)


b = mp.mpf("1.7")
base = lambda t: (mp.sin(t), b * mp.cos(t))


def run(seed):
    _rng.seed(seed)
    A1, A2, A3 = rand_GL2(), rand_GL2(), rand_GL2()
    d0 = (mp.mpf(str(_rng.random())) - mp.mpf("0.5")) * mp.mpf("1.5")
    d1 = (mp.mpf(str(_rng.random())) - mp.mpf("0.5")) * mp.mpf("1.5")
    d2 = (mp.mpf(str(_rng.random())) - mp.mpf("0.5")) * mp.mpf("1.5")

    C1 = lin(A1, offset(base, d0))
    C2 = lin(A2, offset(C1, d1))
    C3 = lin(A3, offset(C2, d2))

    t = mp.mpf("0.9") + mp.mpf(str(_rng.random())) * mp.mpf("2.0")

    C3x = mp.diff(lambda s: C3(s)[0], t)
    C3y = mp.diff(lambda s: C3(s)[1], t)

    v = (mp.diff(lambda s: base(s)[0], t), mp.diff(lambda s: base(s)[1], t))
    vp = (mp.diff(lambda s: base(s)[0], t, 2), mp.diff(lambda s: base(s)[1], t, 2))
    K = det(v, vp)

    A_ = [(mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1))]  # identity as flat
    I = ((mp.mpf(1), mp.mpf(0)), (mp.mpf(0), mp.mpf(1)))
    A_list = [I, A1, matmul(A2, A1), matmul(A3, matmul(A2, A1))]
    d_list = [d0, d1, d2]

    # naive (F3) recurrence: fixed minus sign
    Psi_naive = mp.mpf(1)
    # corrected recurrence: sign of Psi_k multiplies the increment
    Psi = mp.mpf(1)
    sigmas = []
    psis = [mp.mpf(1)]
    Qn = None
    for k in range(3):
        Ak = A_list[k]
        Av = (Ak[0][0] * v[0] + Ak[0][1] * v[1], Ak[1][0] * v[0] + Ak[1][1] * v[1])
        Qk = Av[0] ** 2 + Av[1] ** 2
        Dk = (Ak[0][0] * Ak[1][1] - Ak[0][1] * Ak[1][0]) * K / Qk ** mp.mpf("1.5")
        Psi_naive = Psi_naive - d_list[k] * Dk
        if Psi >= 0:
            Psi = Psi - d_list[k] * Dk
        else:
            Psi = Psi + d_list[k] * Dk
        psis.append(Psi)
        sigmas.append(Psi / psis[-2])
        Qn = Qk
    # note: after loop Qn = Q_2; need Q_3 independently
    A3c = A_list[3]
    Av3 = (A3c[0][0] * v[0] + A3c[0][1] * v[1], A3c[1][0] * v[0] + A3c[1][1] * v[1])
    Q3 = Av3[0] ** 2 + Av3[1] ** 2

    pred = smul(Psi, Av3)
    pred_naive = smul(Psi_naive, Av3)
    err_v = norm(vsub(pred, (C3x, C3y)))
    err_naive = norm(vsub(pred_naive, (C3x, C3y)))
    err_abs = abs(norm((C3x, C3y)) - abs(Psi) * mp.sqrt(Q3))
    return err_v, err_naive, err_abs, Psi, mp.sqrt(Q3), sigmas, psis


print("seed | corr vec err | naive vec err | min |Psi_k| | Psi_3")
maxc = mp.mpf(0)
for seed in [1, 2, 3, 42, 99, 1234]:
    ev, evn, ea, Psi, sp, sig, psis = run(seed)
    minpsi = min(abs(p) for p in psis)
    flag = "  <-- near-cusp" if minpsi < mp.mpf("1e-2") else ""
    print(f"{seed:>5} | {mp.nstr(ev, 5):>12} | {mp.nstr(evn, 5):>13} | "
          f"{mp.nstr(minpsi,5):>10} | {mp.nstr(Psi,5)}{flag}")
    maxc = max(maxc, ev)
print("max corrected vector error:", mp.nstr(maxc, 5))
print("PASS (corrected)" if maxc < mp.mpf("1e-30") else "FAIL")
