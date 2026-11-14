"""Numerical walk-through of the octic construction (companion to GUIDE-octic-construction.md).

For a monic octic q with rational coefficients this script carries out, step by step, the
construction that `Pptc/Octic/Main.lean` (`root_Pconstructible_deg8_coeffs`) proves to
exist, and checks every claim the guide makes along the way:

  * branch N2 (two or more conjugate pairs)  -- Pptc/Octic/TwoPairs.lean
  * branch N1 (exactly one conjugate pair)   -- Pptc/Octic/OnePair.lean
  * branch R  (all eight roots real)         -- Pptc/TotallyReal/{Certificate,Main}.lean

The complex roots of q are used only as *scaffolding*, to find rational starting vectors with
the right signs; every quantity that enters the construction afterwards is obtained from the
coefficients of q by field operations and by roots of auxiliary equations of degree <= 6.
The last step (a root of a polynomial of degree <= 7) is not recursed into: the script only
checks that the target root really is a root of the recovery polynomial.

Run:  python3 octic_construct.py          (needs mpmath)
"""

from mpmath import mp, mpf, mpc, polyroots, sqrt, matrix, lu_solve, fabs, re, im, conj

mp.dps = 60
TOL = mpf(10) ** (-30)
N = 8


# ----------------------------------------------------------------------------- basics

def peval(p, x):
    """Evaluate a polynomial given low-to-high."""
    r = mpf(0) if not isinstance(x, mpc) else mpc(0)
    for c in reversed(p):
        r = r * x + c
    return r


def pmul(p, r):
    out = [mpf(0)] * (len(p) + len(r) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(r):
            out[i + j] += a * b
    return out


def roots_of(p):
    """All complex roots of a low-to-high polynomial (leading zeros stripped)."""
    p = list(p)
    while len(p) > 1 and fabs(p[-1]) < TOL:
        p.pop()
    return polyroots(list(reversed(p)), maxsteps=2000, extraprec=400)


def real_roots(p):
    return sorted(re(r) for r in roots_of(p) if fabs(im(r)) < mpf(10) ** (-20))


def rnd(x, den=10 ** 6):
    """Round to a rational with denominator `den` -- the 'rationalise by density' step."""
    return mpf(int(mp.nint(x * den))) / den


def power_sums(q, K):
    """Newton sums s_0..s_K of the monic degree-8 polynomial q (= Tr C^k)."""
    a = q  # a[i] = coeff of x^i, a[8] = 1
    s = [mpf(N)]
    for k in range(1, K + 1):
        if k <= N:
            v = -k * a[N - k]
            for j in range(1, k):
                v -= a[N - j] * s[k - j]
        else:
            v = mpf(0)
            for j in range(1, N + 1):
                v -= a[N - j] * s[k - j]
        s.append(v)
    return s


def companion(q):
    C = matrix(N, N)
    for i in range(N - 1):
        C[i, i + 1] = 1
    for j in range(N):
        C[N - 1, j] = -q[j]
    return C


def charpoly(M):
    """Faddeev-LeVerrier: coefficients (low-to-high) of det(t - M), field operations only."""
    n = M.rows
    c = [mpf(0)] * (n + 1)
    c[n] = mpf(1)
    A = matrix(n, n)
    I = mp.eye(n)
    for k in range(1, n + 1):
        A = M * A + c[n - k + 1] * I
        MA = M * A
        c[n - k] = -sum(MA[i, i] for i in range(n)) / k
    return c


def poly_at_matrix(phi, C):
    out = matrix(N, N)
    P = mp.eye(N)
    for c in phi:
        out += c * P
        P = P * C
    return out


# ----------------------------------------------------------------------------- trace form

class TraceForm:
    """Trace form data of q on coefficient vectors (Fin 8) and on the b-basis (Fin 7)."""

    def __init__(self, q):
        self.q = q
        self.s = power_sums(q, 21)

    # --- on coefficient vectors v in R^8 (phi = sum v_i X^i)
    def p1(self, v):
        return sum(self.s[i] * v[i] for i in range(N))

    def H(self, u, v):
        return sum(u[i] * v[j] * self.s[i + j] for i in range(N) for j in range(N))

    def T(self, u, v, w):
        return sum(u[i] * v[j] * w[k] * self.s[i + j + k]
                   for i in range(N) for j in range(N) for k in range(N))

    def p3(self, v):
        return self.T(v, v, v)

    # --- the trace-zero hyperplane, coordinates x in R^7
    def L(self, x):
        """Lcomb8: x -> coefficient vector with Tr = 0."""
        return [-sum(x[j] * self.s[j + 1] for j in range(7)) / N] + list(x)

    def B(self, x, y):
        return self.H(self.L(x), self.L(y))

    def Q(self, x):
        return self.B(x, x)

    def stereo(self, P0, x):
        qx, bx = self.Q(x), self.B(P0, x)
        return [qx * P0[i] - 2 * bx * x[i] for i in range(7)]

    def Phi(self, P0, x):
        return self.p3(self.L(self.stereo(P0, x)))


def interpolant(q, rts, z, c):
    """Real f, deg <= 7, with f(z) = c, f(conj z) = conj c, f = 0 at the other roots of q."""
    G = [mpf(1)]
    for r in rts:
        if fabs(r - z) > TOL and fabs(r - conj(z)) > TOL:
            G = pmul(G, [-r, 1])
    G = [re(g) for g in G]
    w = c / peval(G, z)
    h1 = im(w) / im(z)
    h0 = re(w) - h1 * re(z)
    return pmul(G, [h0, h1])


def lagrange_real(q, rts, xj, z, c):
    """Real X, deg <= 7: 1 at the real root xj, 0 at the other real roots, c at z, conj c at conj z."""
    Lp = [mpf(1)]
    for r in rts:
        if fabs(r - xj) > TOL:
            Lp = pmul(Lp, [-r, 1])
    Lp = [re(g) for g in Lp]
    Lp = [g / peval(Lp, xj) for g in Lp]          # 1 at xj, 0 at every other root
    corr = interpolant(q, rts, z, c)              # c at z, 0 at every real root
    return [Lp[i] + corr[i] for i in range(N)]


def coeff7(f):
    f = list(f) + [mpf(0)] * (N - len(f))
    return f[1:N]


def pos_quadratic_root(a, b, c):
    """Positive root of a t^2 + 2 b t + c with a > 0 > c (exists_pos_quadratic_root)."""
    assert a > 0 > c
    return (-b + sqrt(b * b - a * c)) / a


def cone_point(tf, q, rts, z):
    """Steps C1-C3 of the guide: rational e (Q<0), rational f (Q>0), P0 = e + t f on the cone."""
    e = [rnd(v) for v in coeff7(interpolant(q, rts, z, mpc(0, 1)))]
    fp = interpolant(q, rts, z, mpc(1, 0))
    fp[0] -= mpf(2) / 8
    f = [rnd(v) for v in coeff7(fp)]
    assert tf.Q(e) < 0 < tf.Q(f), "rationalisation too coarse"
    t = pos_quadratic_root(tf.Q(f), tf.B(e, f), tf.Q(e))
    P0 = [e[i] + t * f[i] for i in range(7)]
    assert fabs(tf.Q(P0)) < TOL
    return P0


def prem(a, b):
    """Remainder of a by b (low-to-high, floating: leading coefficients below EPS are dropped)."""
    a = list(a)
    while len(a) >= len(b):
        f = a[-1] / b[-1]
        for i in range(len(b)):
            a[len(a) - len(b) + i] -= f * b[i]
        a.pop()
    return strip(a)


EPS = mpf(10) ** (-25)


def strip(p):
    p = list(p)
    while p and fabs(p[-1]) < EPS:
        p.pop()
    return p


def gcd_shortcut(q, phi, y, beta, rts):
    """If phi(beta) differs from phi at the other roots, gcd(q, phi - y) = X - beta.

    Returns True when the shortcut applies (and then checks it), False otherwise.
    Not part of the Lean proof, which always recurses into the degree-7 theorem."""
    vals = [peval(phi, r) for r in rts]
    if sum(1 for v in vals if fabs(v - y) < mpf(10) ** (-8)) != 1:
        return False
    a, b = strip(q), list(phi)
    b[0] -= y
    b = strip(b)
    while True:
        r = prem(a, b)
        if not r:
            break
        a, b = b, r
    assert len(b) == 2 and fabs(-b[0] / b[1] - beta) < mpf(10) ** (-15), (len(b), b)
    return True


def tail(tf, q, rts, phi, label):
    """Steps T1-T3: resolvent, quartic power law, recovery polynomial."""
    C = companion(q)
    Nm = poly_at_matrix(phi, C)
    R = charpoly(Nm)
    assert all(fabs(R[k]) < TOL * max(1, max(fabs(c) for c in R)) for k in (5, 6, 7)), R[5:8]
    c = [-R[k] for k in range(5)]
    short = []
    for beta in [re(r) for r in rts if fabs(im(r)) < TOL]:
        y = peval(phi, beta)
        scale = max(mpf(1), fabs(y) ** 8)
        assert fabs(y ** 8 - sum(c[k] * y ** k for k in range(5))) < TOL * scale
        # y is a crossing of  Y = X^8  with  Y = c4 X^4 + ... + c0
        rec = list(phi)
        rec[0] -= y
        assert fabs(peval(rec, beta)) < TOL * scale
        short.append(gcd_shortcut(q, phi, y, beta, rts))
    assert max(fabs(v) for v in phi[1:]) > TOL, "phi must be nonconstant"
    print(f"  [{label}] resolvent: y^8 = c4 y^4 + c3 y^3 + c2 y^2 + c1 y + c0 with")
    for k in range(4, -1, -1):
        print(f"      c{k} = {mp.nstr(c[k], 18)}")
    print(f"  [{label}] all real roots beta satisfy the power law at y = phi(beta); OK")
    print(f"  [{label}] gcd shortcut beta = -r0/r1 from gcd(q, phi - y) applies at"
          f" {sum(short)} of {len(short)} real roots")


# ----------------------------------------------------------------------------- branch N2

def branch_two_pairs(q, rts, z, w):
    tf = TraceForm(q)
    P0 = cone_point(tf, q, rts, z)

    # negative and positive definite 2-planes from the two pairs
    v1 = coeff7(interpolant(q, rts, z, mpc(0, 1)))
    v2 = coeff7(interpolant(q, rts, w, mpc(0, 1)))
    g1 = interpolant(q, rts, z, mpc(1, 0)); g1[0] -= mpf(1) / 4
    g2 = interpolant(q, rts, w, mpc(1, 0)); g2[0] -= mpf(1) / 4
    w1, w2 = coeff7(g1), coeff7(g2)

    # the P-constructible projection  pi(y) = c y - B(P0,y) u  onto P0-perp
    unit = lambda i: [mpf(1) if j == i else mpf(0) for j in range(7)]
    i0 = next(i for i in range(7) if fabs(tf.B(P0, unit(i))) > mpf(10) ** (-6))
    cproj, u = tf.B(P0, unit(i0)), unit(i0)
    proj = lambda y: [cproj * y[i] - tf.B(P0, y) * u[i] for i in range(7)]

    def orth_combo(a, b):
        ba, bb = tf.B(P0, a), tf.B(P0, b)
        return [bb * a[i] - ba * b[i] for i in range(7)]

    e0, f0 = orth_combo(v1, v2), orth_combo(w1, w2)
    # rescale before rounding so the rounding error is relatively small
    ne, nf = max(fabs(v) for v in e0), max(fabs(v) for v in f0)
    e = proj([rnd(v / ne) for v in e0])
    f = proj([rnd(v / nf) for v in f0])
    assert fabs(tf.B(P0, e)) < TOL and fabs(tf.B(P0, f)) < TOL
    assert tf.Q(e) < 0 < tf.Q(f)

    t = pos_quadratic_root(tf.Q(f), tf.B(e, f), tf.Q(e))
    x = [e[i] + t * f[i] for i in range(7)]
    assert fabs(tf.Q(x)) < TOL and fabs(tf.B(P0, x)) < TOL

    cv, cw = tf.L(P0), tf.L(x)
    a, b, c, d = tf.p3(cv), 3 * tf.T(cv, cv, cw), 3 * tf.T(cv, cw, cw), tf.p3(cw)
    # binary cubic a s^3 + b s^2 t + c s t^2 + d t^3 = 0 with s = 1
    if fabs(d) < TOL:
        s_, t_ = mpf(0), mpf(1)
    else:
        s_, t_ = mpf(1), real_roots([a, b, c, d])[0]
    psi = [s_ * cv[i] + t_ * cw[i] for i in range(N)]
    for name, val in (("Tr phi", tf.p1(psi)), ("Tr phi^2", tf.H(psi, psi)), ("Tr phi^3", tf.p3(psi))):
        assert fabs(val) < TOL * max(1, max(fabs(v) for v in psi) ** 3), (name, val)
    print("  [N2] Tschirnhaus phi (low-to-high):", [mp.nstr(v, 10) for v in psi])
    tail(tf, q, rts, psi, "N2")


# ----------------------------------------------------------------------------- branch N1

def branch_one_pair(q, rts, z):
    tf = TraceForm(q)
    P0 = cone_point(tf, q, rts, z)
    reals = [re(r) for r in rts if fabs(im(r)) < TOL]
    omega = mpc(-0.5, sqrt(3) / 2)

    cands = []
    for xj in reals[:2]:
        for c in (omega, conj(omega)):
            X = lagrange_real(q, rts, xj, z, c)
            d = coeff7(X)
            # certificate values promised by exists_direction_of_value8
            assert fabs(tf.Q(d)) < TOL * 10 ** 6 and fabs(tf.p3(tf.L(d)) - 3) < TOL * 10 ** 6
            cands.append((tf.Phi(P0, d), d))
    dplus = max(cands, key=lambda p: p[0])
    dminus = min(cands, key=lambda p: p[0])
    assert dplus[0] > 0 > dminus[0], "sign certificate failed"

    def rationalise(d, sign):
        nd = max(fabs(v) for v in d)
        for den in (10 ** 6, 10 ** 9, 10 ** 12, 10 ** 15):
            r = [rnd(v / nd, den) for v in d]
            if sign * tf.Phi(P0, r) > 0:
                return r
        raise AssertionError("rationalisation failed")

    dp, dm = rationalise(dplus[1], 1), rationalise(dminus[1], -1)
    delta = [dm[i] - dp[i] for i in range(7)]

    # the sextic Psi(m) = p3(L(stereo(P0, dp + m delta))): interpolate at 7 nodes
    nodes = [mpf(k) / 6 for k in range(7)]
    vals = [tf.Phi(P0, [dp[i] + m * delta[i] for i in range(7)]) for m in nodes]
    V = matrix(7, 7)
    for i, m in enumerate(nodes):
        for k in range(7):
            V[i, k] = m ** k
    Psi = list(lu_solve(V, matrix(vals)))
    assert peval(Psi, mpf(0)) > 0 > peval(Psi, mpf(1))
    # independent check that Psi really has degree <= 6
    mtest = mpf(7) / 3
    assert fabs(peval(Psi, mtest) - tf.Phi(P0, [dp[i] + mtest * delta[i] for i in range(7)])) \
        < TOL * 10 ** 10 * max(1, fabs(peval(Psi, mtest)))
    mstar = next(m for m in real_roots(Psi) if 0 < m < 1)
    xstar = [dp[i] + mstar * delta[i] for i in range(7)]
    vstar = tf.stereo(P0, xstar)
    assert max(fabs(v) for v in vstar) > mpf(10) ** (-12), "vstar = 0"
    psi = tf.L(vstar)
    scale = max(1, max(fabs(v) for v in psi) ** 3)
    for name, val in (("Tr phi", tf.p1(psi)), ("Tr phi^2", tf.H(psi, psi)), ("Tr phi^3", tf.p3(psi))):
        assert fabs(val) < mpf(10) ** (-20) * scale, (name, val)
    print(f"  [N1] sextic parameter m* = {mp.nstr(mstar, 20)}")
    print("  [N1] Tschirnhaus phi (low-to-high):", [mp.nstr(v, 10) for v in psi])
    tail(tf, q, rts, psi, "N1")


# ----------------------------------------------------------------------------- branch R

CENTRE8 = dict(
    a=[-4, -2, 2, -1, 1, 4, 1, -1],
    b=[0, 3, 0, 2, 1, -1, -6, 1],
    g=[1, mpf(-2) / 3, 0, -1, 1, mpf(3) / 2, mpf(2) / 3, mpf(-5) / 2],
    w1=[mpf(-143) / 21, mpf(-113) / 21, mpf(-22) / 21, mpf(-452) / 63, mpf(-18) / 7,
        mpf(170) / 21, mpf(-24) / 7, mpf(1154) / 63],
    w2=[mpf(38) / 35, mpf(29) / 35, mpf(1) / 35, mpf(137) / 105, mpf(96) / 35, mpf(-44) / 35,
        mpf(156) / 35, mpf(-193) / 21],
    w3=[mpf(167) / 35, mpf(-89) / 35, mpf(184) / 35, mpf(-272) / 105, mpf(-501) / 35,
        mpf(-186) / 35, mpf(-101) / 35, mpf(370) / 21],
)
CENTRE8_ROOTS = (mpf(0), mpf(5) / 3, mpf(-5322) / 2915, mpf(-1))


def nearest(cands, target):
    return min(cands, key=lambda r: fabs(r - target))


def fit_poly(fn, deg):
    nodes = [mpf(k) - deg / mpf(2) for k in range(deg + 1)]
    V = matrix(deg + 1, deg + 1)
    for i, m in enumerate(nodes):
        for k in range(deg + 1):
            V[i, k] = m ** k
    return list(lu_solve(V, matrix([fn(m) for m in nodes])))


def branch_totally_real(q, rts):
    tf = TraceForm(q)
    alphas = sorted(re(r) for r in rts)
    V = matrix(N, N)
    for i, al in enumerate(alphas):
        for k in range(N):
            V[i, k] = al ** k

    # b-space inputs: pull the centre back through the Vandermonde map, round, trace-correct
    inp = {}
    for key, yv in CENTRE8.items():
        bvec = [rnd(v, 10 ** 12) for v in lu_solve(V, matrix([mpf(v) for v in yv]))]
        bvec[0] -= tf.p1(bvec) / N              # correctSlot: now S1(y(b)) = Tr b(C) = 0
        inp[key] = bvec

    # the symmetric pairings, all computed from power sums of q (no roots)
    S3 = tf.p3
    NB = lambda P, w: tf.T(P, P, w)            # sum_i YP_i^2 Yw_i
    conic = lambda P, u: tf.T(P, u, u)         # sum_i YP_i Yu_i^2
    Bd = tf.T                                  # sum_i YP_i Yu_i Yv_i
    add = lambda u, v, s=1: [u[i] + s * v[i] for i in range(N)]

    def S5(v):
        y = [peval(v, al) for al in alphas]    # (check only; = Tr v(C)^5)
        return sum(t ** 5 for t in y)

    def tr5(v):
        M = poly_at_matrix(v, companion(q))
        M2 = M * M
        M5 = M2 * M2 * M
        return sum(M5[i, i] for i in range(N))

    lam0, x0, mu0, kap0 = CENTRE8_ROOTS

    # step 1: cubic in lambda
    p1 = fit_poly(lambda l: S3(add(inp["a"], inp["b"], l)), 3)
    lam = nearest(real_roots(p1), lam0)
    P = add(inp["a"], inp["b"], lam)
    assert fabs(NB(P, inp["g"])) > mpf(10) ** (-6)
    projN = lambda w: add(w, inp["g"], -NB(P, w) / NB(P, inp["g"]))
    W1, W2, W3 = projN(inp["w1"]), projN(inp["w2"]), projN(inp["w3"])

    # step 2: quadratic in x
    p2 = fit_poly(lambda x: conic(P, add(W1, W2, x)), 2)
    x = nearest(real_roots(p2), x0)
    q0 = add(W1, W2, x)

    # step 3: sextic in mu (denominator cleared)
    def cleared(mu):
        d = add(W3, W1, mu)
        vec = add([Bd(P, d, d) * t for t in q0], d, -2 * Bd(P, q0, d))
        return S3(vec)
    p3 = fit_poly(cleared, 6)
    mu = nearest(real_roots(p3), mu0)
    d = add(W3, W1, mu)
    assert fabs(Bd(P, d, d)) > mpf(10) ** (-6)
    v = add(q0, d, -2 * Bd(P, q0, d) / Bd(P, d, d))

    # step 4: quintic in kappa
    p4 = fit_poly(lambda k: tr5(add(P, v, k)), 5)
    kap = nearest(real_roots(p4), kap0)
    out = add(P, v, kap)

    y = [peval(out, al) for al in alphas]
    for k in (1, 3, 5):
        assert fabs(sum(t ** k for t in y)) < mpf(10) ** (-20), (k, sum(t ** k for t in y))
    assert min(fabs(y[i] - y[j]) for i in range(N) for j in range(i)) > mpf(10) ** (-3)
    print("  [R] step roots (lambda, x, mu, kappa) =",
          [mp.nstr(t, 12) for t in (lam, x, mu, kap)])
    print("  [R] y-vector of the output:", [mp.nstr(t, 8) for t in y])

    R = charpoly(poly_at_matrix(out, companion(q)))
    assert all(fabs(R[k]) < mpf(10) ** (-20) for k in (7, 5, 3)), [R[7], R[5], R[3]]
    # chi(t) = Qq(t^2) - e7 t,  Qq(x) = x^4 + R6 x^3 + R4 x^2 + R2 x + R0,  e7 = -R1
    Qq = [R[0], R[2], R[4], R[6], mpf(1)]
    c = -R[1]
    for al in alphas:
        beta = peval(out, al)
        assert fabs(peval(Qq, beta ** 2) - c * beta) < mpf(10) ** (-20) * max(1, beta ** 8)
        rec = list(out)
        rec[0] -= beta
        assert fabs(peval(rec, al)) < mpf(10) ** (-20)
        assert gcd_shortcut(q, out, beta, al, rts)
    print("  [R] chi(t) = Q(t^2) - c t with Q = x^4 +",
          " + ".join(f"({mp.nstr(Qq[k], 10)}) x^{k}" for k in (3, 2, 1, 0)),
          f", c = {mp.nstr(c, 10)}")
    print("  [R] every root alpha: Q(beta^2) = c beta at beta = Phi_b(alpha), and alpha solves"
          " Phi_b(X) = beta; OK")


# ----------------------------------------------------------------------------- driver

def construct(q_int):
    q = [mpf(c) for c in q_int]
    assert len(q) == 9 and q[8] == 1
    rts = roots_of(q)
    assert min(fabs(rts[i] - rts[j]) for i in range(N) for j in range(i)) > mpf(10) ** (-10), \
        "q is not separable: split off gcd(q, q') first"
    upper = [r for r in rts if im(r) > mpf(10) ** (-20)]
    print(f"q = {q_int}  (low-to-high);  {N - 2 * len(upper)} real roots, {len(upper)} conjugate pairs")
    if len(upper) == 0:
        branch_totally_real(q, rts)
    elif len(upper) == 1:
        branch_one_pair(q, rts, upper[0])
    else:
        branch_two_pairs(q, rts, upper[0], upper[1])


if __name__ == "__main__":
    examples = [
        # x^8 - x - 1 : two real roots, three pairs
        [-1, -1, 0, 0, 0, 0, 0, 0, 1],
        # two pairs, four real roots: (x^2+1)(x^2+4)(x^2-1)(x^2-4) + x
        [16, 1, 0, 0, -17, 0, 0, 0, 1],
        # one pair, six real roots
        [5, -3, -19, 2, 21, 1, -9, 0, 1],
        # one pair: (x^2+1)(x^2-1)(x^2-4)(x^2-9) + x
        [-36, 1, 13, 0, 35, 0, -13, 0, 1],
        # one pair, no symmetry
        [-7, 5, 31, -6, -29, 3, 2, -2, 1],
        # totally real: (x^2-1)(x^2-4)(x^2-9)(x^2-16) + x
        [576, 1, -820, 0, 273, 0, -30, 0, 1],
        # totally real, no symmetry: prod_{k=-3..4}(x-k) + 1
        None,
    ]
    p = [mpf(1)]
    for k in range(-3, 5):
        p = pmul(p, [mpf(-k), mpf(1)])
    p[0] += 1
    examples[-1] = [int(c) for c in p]
    for ex in examples:
        construct(ex)
        print()
    print("all checks passed")
