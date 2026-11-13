"""F1 stage A: invariants of W_2 = (C^ x C^)/(S_d x <iota>) for the engine
covers, where C^ is the Galois closure of g: P^1 -> P^1 (three branch points,
monodromy S_d), S_d acts diagonally and iota swaps the factors.

Computes, exactly (Fractions / exact cyclotomic exponents; the only floating
point is the Eichler trace, rounded with an explicit tolerance check):
  g(C^)                    Riemann-Hurwitz;
  p_g(S) = dim (Lambda^2 V)^{S_d},  V = H^0(C^, K) as S_d-module (Eichler trace);
  q(S)   = dim V^{S_d} = 0;
  e(W)   = (1/|Gamma|) sum_gamma e(X^gamma);
  K_W^2  = (K_X - R)^2/|Gamma|, R = sum of the fixed curves {(P, s P)}, s^2 = 1;
  every singular point of W, its local group, its type 1/N(1,q) after removing
  reflections, and its Hirzebruch-Jung resolution;
  K_S^2 of the minimal resolution S two ways:
      Noether:  12 chi(O_S) - e(S),   e(S) = e(W) + sum r_x,
      local:    K_W^2 - sum delta_x,  delta_x = -(sum a_i E_i)^2.
Agreement of the two is the check on the local analysis.  If K_S^2 > 0 and
p_g >= 1 then S is of general type (minimal model has K^2 >= K_S^2 > 0 and
kappa >= 0).

Usage: python3 F1_kodaira.py        (Windows: py -3 F1_kodaira.py)
"""

import cmath
import sys
from fractions import Fraction as Fr
from itertools import permutations
from math import gcd

# ----------------------------------------------------------------------------
# permutations
# ----------------------------------------------------------------------------


def mul(a, b):  # (a b)(i) = a(b(i))
    return tuple(a[i] for i in b)


def inv(a):
    r = [0] * len(a)
    for i, j in enumerate(a):
        r[j] = i
    return tuple(r)


def cycle_type(a):
    seen, out = set(), []
    for i in range(len(a)):
        if i in seen:
            continue
        k, j = 0, i
        while j not in seen:
            seen.add(j)
            j = a[j]
            k += 1
        out.append(k)
    return tuple(sorted(out, reverse=True))


def order(a):
    o = 1
    for c in cycle_type(a):
        o = o * c // gcd(o, c)
    return o


def power(a, k):
    r = tuple(range(len(a)))
    for _ in range(k % order(a)):
        r = mul(a, r)
    return r


def generated_size(gens, d):
    e = tuple(range(d))
    seen = {e}
    frontier = [e]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = mul(g, x)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
        frontier = new
    return len(seen)


def find_triples(t0, tinf, d):
    """Triples (s0, s1, sinf) with s0 s1 sinf = 1, s1 a transposition,
    cycle types t0, tinf, generating S_d; up to simultaneous conjugation we
    fix sinf to a canonical element and return all s1 that work, with the
    number of classes (conjugation by the centraliser of sinf)."""
    # canonical sinf of type tinf
    cyc, pos = [], 0
    for c in tinf:
        cyc.append(list(range(pos, pos + c)))
        pos += c
    sinf = list(range(d))
    for cy in cyc:
        for i, x in enumerate(cy):
            sinf[x] = cy[(i + 1) % len(cy)]
    sinf = tuple(sinf)
    out = []
    fact = 1
    for k in range(2, d + 1):
        fact *= k
    for i in range(d):
        for j in range(i + 1, d):
            s1 = list(range(d))
            s1[i], s1[j] = j, i
            s1 = tuple(s1)
            s0 = inv(mul(s1, sinf))
            if cycle_type(s0) != tuple(sorted(t0, reverse=True)):
                continue
            if generated_size([s0, s1], d) != fact:
                continue
            out.append((s0, s1, sinf))
    return out


# ----------------------------------------------------------------------------
# the curve C^: points over branch values = cosets g<s_b>
# ----------------------------------------------------------------------------


class Cover:
    def __init__(self, triple, d):
        self.d = d
        self.G = list(permutations(range(d)))
        self.idx = {g: i for i, g in enumerate(self.G)}
        self.gens = list(triple)  # s_b for b = 0, 1 (the transposition), inf
        self.e = [order(s) for s in self.gens]
        self.N = len(self.G)
        self.class_size = {}
        for g in self.G:
            t = cycle_type(g)
            self.class_size[t] = self.class_size.get(t, 0) + 1
        self.genus = 1 + Fr(self.N, 2) * (1 - sum(Fr(1, e) for e in self.e))
        assert self.genus.denominator == 1
        self.genus = int(self.genus)
        # cyclic subgroups and coset data
        self.cyc = []
        for s in self.gens:
            pw = [power(s, k) for k in range(order(s))]
            self.cyc.append(pw)
        # coset id and representative for each branch b
        self.coset_of = []
        self.rep = []
        for b in range(3):
            cid = {}
            reps = []
            for g in self.G:
                if g in cid:
                    continue
                k = len(reps)
                reps.append(g)
                for s in self.cyc[b]:
                    cid[mul(g, s)] = k
            self.coset_of.append(cid)
            self.rep.append(reps)

    def act(self, mu, b, k):
        """mu * (point k over b) -> (point index, exponent j) with
        mu g_k = g_{k'} s_b^j; the derivative of mu at that point, in the
        standard coordinates, is zeta_{e_b}^j."""
        g = self.rep[b][k]
        mg = mul(mu, g)
        k2 = self.coset_of[b][mg]
        s = mul(inv(self.rep[b][k2]), mg)
        j = self.cyc[b].index(s)
        return k2, j

    def fixed_data(self, mu):
        """Fixed points of mu != 1 by class: list of (b, j, count).  mu fixes
        g P_b iff g^-1 mu g = s_b^j, and then its derivative there is
        zeta_{e_b}^j; for each j with s_b^j conjugate to mu there are
        |C(mu)|/e_b such points (e_b choices of g per point)."""
        t = cycle_type(mu)
        cent = self.N // self.class_size[t]
        out = []
        for b in range(3):
            for j in range(1, self.e[b]):
                if cycle_type(self.cyc[b][j]) == t:
                    assert cent % self.e[b] == 0
                    out.append((b, j, cent // self.e[b]))
        return out

    def nfix(self, mu):
        return sum(c for _, _, c in self.fixed_data(mu))

    def chi_V(self, mu):
        """Eichler trace formula: tr(mu | H^0(K)) = 1 + sum a/(1-a), a the
        derivative at each fixed point; g for the identity."""
        if mu == tuple(range(self.d)):
            return complex(self.genus)
        tot = 1 + 0j
        for b, j, cnt in self.fixed_data(mu):
            a = cmath.exp(2j * cmath.pi * j / self.e[b])
            tot += cnt * a / (1 - a)
        return tot


# ----------------------------------------------------------------------------
# global invariants
# ----------------------------------------------------------------------------


def global_invariants(C):
    G, N, g = C.G, C.N, C.genus
    ident = tuple(range(C.d))
    # one representative per class
    reps = {}
    for mu in G:
        reps.setdefault(cycle_type(mu), mu)
    chi = {t: C.chi_V(mu) for t, mu in reps.items()}
    nfix = {t: (None if mu == ident else C.nfix(mu)) for t, mu in reps.items()}
    sq = {t: cycle_type(mul(mu, mu)) for t, mu in reps.items()}
    w = C.class_size
    s1 = sum(w[t] * chi[t] for t in reps) / N
    assert abs(s1) < 1e-6, s1                     # <chi_V, 1> = genus(P^1) = 0
    assert all(abs(c.imag) < 1e-6 for c in chi.values())
    pg_Z = sum(w[t] * chi[t] ** 2 for t in reps) / N
    pg_W = sum(w[t] * (chi[t] ** 2 - chi[sq[t]]) / 2 for t in reps) / N
    for v in (pg_Z, pg_W):
        assert abs(v.imag) < 1e-6 and abs(v.real - round(v.real)) < 1e-6, v
    pg_Z, pg_W = int(round(pg_Z.real)), int(round(pg_W.real))
    tid = cycle_type(ident)
    # Euler number of W: (1/|Gamma|) sum_gamma e(X^gamma), |Gamma| = 2 N
    eX = (2 - 2 * g) ** 2
    tot = Fr(eX)
    for t in reps:
        if t != tid:
            tot += w[t] * nfix[t] ** 2                 # (mu, 1)
        if sq[t] == tid:
            tot += w[t] * (2 - 2 * g)                  # (mu, iota): curve ~ C^
        else:
            tot += w[t] * nfix[sq[t]]                  # isolated points
    eW = tot / (2 * N)
    eZ = (Fr(eX) + sum(w[t] * nfix[t] ** 2 for t in reps if t != tid)) / N
    # K_W^2 = (K_X - R)^2 / |Gamma|
    invol = [mu for mu in G if mul(mu, mu) == ident]  # includes identity
    I = len(invol)
    K2X = 2 * (2 * g - 2) ** 2
    RR = I * (2 - 2 * g)
    for a in invol:
        ia = inv(a)
        for b in invol:
            if a != b:
                RR += nfix[cycle_type(mul(ia, b))]
    KR = I * (4 * g - 4)
    K2W = Fr(K2X - 2 * KR + RR, 2 * N)
    K2Z = Fr(K2X, N)
    return dict(g=g, pg_W=pg_W, pg_Z=pg_Z, eW=eW, eZ=eZ, K2W=K2W, K2Z=K2Z,
                n_invol=I)


# ----------------------------------------------------------------------------
# local groups: monomial 2x2 matrices with root-of-unity entries, written
# additively: ('d', u, v) = diag(e(u), e(v)); ('a', u, v) = [[0, e(u)], [e(v), 0]]
# with u, v in Q/Z.
# ----------------------------------------------------------------------------


def m_norm(m):
    return (m[0], m[1] % 1, m[2] % 1)


def m_mul(A, B):
    # matrices act on column vectors; (A B) x = A (B x)
    ta, a1, a2 = A
    tb, b1, b2 = B
    if ta == "d" and tb == "d":
        return m_norm(("d", a1 + b1, a2 + b2))
    if ta == "d" and tb == "a":
        # diag(a1,a2) [[0,b1],[b2,0]] = [[0, a1 b1],[a2 b2, 0]]
        return m_norm(("a", a1 + b1, a2 + b2))
    if ta == "a" and tb == "d":
        # [[0,a1],[a2,0]] diag(b1,b2) = [[0, a1 b2],[a2 b1, 0]]
        return m_norm(("a", a1 + b2, a2 + b1))
    # [[0,a1],[a2,0]] [[0,b1],[b2,0]] = diag(a1 b2, a2 b1)
    return m_norm(("d", a1 + b2, a2 + b1))


def closure(gens):
    I = ("d", Fr(0), Fr(0))
    seen = {I}
    frontier = [I]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = m_mul(g, x)
                if y not in seen:
                    seen.add(y)
                    new.append(y)
        frontier = new
    return seen


def is_reflection(m):
    t, u, v = m
    if t == "d":
        return (u == 0) != (v == 0)
    return (u + v) % 1 == 0  # eigenvalues +-sqrt(e(u+v)); reflection iff e(u+v) = 1


def conj_diag(m, t):
    """Conjugate by D = diag(1, e(t)): D m D^-1."""
    D = ("d", Fr(0), Fr(t))
    Di = ("d", Fr(0), Fr(-t))
    return m_mul(m_mul(D, m), Di)


def lcm(a, b):
    return a * b // gcd(a, b)


def denom_lcm(vals):
    n = 1
    for x in vals:
        n = lcm(n, Fr(x).denominator)
    return n


def remove_reflections(H):
    """Return the cyclic group H' (as a set of ('d', u, v)) acting on
    C^2/R(H) = C^2 with no reflections, by repeatedly quotienting by the
    reflection subgroup.  Raises if a case outside the handled ones occurs."""
    for _ in range(6):
        refl = [m for m in H if is_reflection(m)]
        if not refl:
            return H
        R = closure(refl)
        anti = [m for m in R if m[0] == "a"]
        if not anti:
            # R = mu_n1 x mu_n2 diagonal; quotient (z, w) -> (z^n1, w^n2)
            n1 = denom_lcm([m[1] for m in R])
            n2 = denom_lcm([m[2] for m in R])
            assert len(R) == n1 * n2
            newH = set()
            for m in H:
                t, u, v = m
                if t == "d":
                    newH.add(m_norm(("d", n1 * u, n2 * v)))
                else:
                    assert n1 == n2, "antidiagonal element does not normalise R"
                    newH.add(m_norm(("a", n1 * u, n1 * v)))
            H = newH
            continue
        # R contains an antidiagonal reflection: conjugate it to the swap
        s = anti[0]
        t = s[1]
        H = {conj_diag(m, t) for m in H}
        R = {conj_diag(m, t) for m in R}
        assert ("a", Fr(0), Fr(0)) in R
        # R = G(n, p, 2): entries in mu_n, entry sums in mu_{n/p}
        n = denom_lcm([x for m in R for x in (m[1], m[2])])
        sums = {(m[1] + m[2]) % 1 for m in R}
        np_ = denom_lcm(list(sums))
        p = n // np_
        assert len(R) == 2 * n * n // p, ("R not G(n,p,2)", len(R), n, p)
        assert len(sums) == np_
        # invariants u = z^n + w^n (deg n), v = (z w)^(n/p) (deg 2n/p)
        newH = set()
        for m in H:
            tt, a, b = m
            # proportionality of u requires n a = n b mod 1
            assert (n * a - n * b) % 1 == 0, "H does not act diagonally on (u, v)"
            newH.add(m_norm(("d", n * a, np_ * (a + b))))
        H = newH
    raise RuntimeError("reflection removal did not terminate")


def cyclic_type(H):
    """H diagonal without reflections, hence cyclic: return (N, q) with H
    generated by diag(e(1/N), e(q/N)), 0 < q < N, gcd(q, N) = 1."""
    N = len(H)
    if N == 1:
        return (1, 0)
    for m in H:
        t, u, v = m
        assert t == "d"
        if Fr(u).denominator == N:
            # generator; normalise first exponent to 1/N
            k = int(u * N)
            kinv = pow(k, -1, N)
            q = int((v * N * kinv) % N)
            assert gcd(q, N) == 1
            return (N, q)
    raise RuntimeError("not cyclic?")


def hj(N, q):
    """Hirzebruch-Jung continued fraction N/q = [b1, ..., br]."""
    out = []
    a, b = N, q
    while b:
        c = -(-a // b)
        out.append(c)
        a, b = b, c * b - a
    return out


def delta_and_r(N, q):
    """For 1/N(1,q): r = number of exceptional curves and
    delta = -(sum a_i E_i)^2 >= 0 with K_S = f^* K_W + sum a_i E_i."""
    if N == 1:
        return 0, Fr(0)
    bs = hj(N, q)
    r = len(bs)
    # solve sum_j a_j (E_j . E_i) = b_i - 2  (adjunction K.E_i = b_i - 2)
    M = [[Fr(0)] * r for _ in range(r)]
    for i in range(r):
        M[i][i] = Fr(-bs[i])
        if i + 1 < r:
            M[i][i + 1] = M[i + 1][i] = Fr(1)
    rhs = [Fr(b - 2) for b in bs]
    a = solve(M, rhs)
    delta = -sum(a[i] * rhs[i] for i in range(r))
    return r, delta


def solve(M, rhs):
    n = len(M)
    A = [row[:] + [rhs[i]] for i, row in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if A[i][c] != 0)
        A[c], A[p] = A[p], A[c]
        for i in range(n):
            if i != c and A[i][c] != 0:
                f = A[i][c] / A[c][c]
                A[i] = [x - f * y for x, y in zip(A[i], A[c])]
    return [A[i][n] / A[i][i] for i in range(n)]


# ----------------------------------------------------------------------------
# singular points of W
# ----------------------------------------------------------------------------


def singular_points(C):
    """Gamma-orbits of points (P, Q), P over branch b, Q over branch b',
    with their local groups in GL_2 (standard coordinates)."""
    ident = tuple(range(C.d))
    out = []
    for b in range(3):
        for b2 in range(b, 3):
            seen = set()
            nQ = len(C.rep[b2])
            # S_d-orbits on F_b x F_b2: fix P = point 0 over b (rep = identity)
            assert C.rep[b][0] == ident
            stabP = C.cyc[b]
            for kq in range(nQ):
                if (b, b2, kq) in seen:
                    continue
                # orbit of (P0, Q_kq) under Stab(P0) gives the same W-point
                orb = {C.act(s, b2, kq)[0] for s in stabP}
                for k in orb:
                    seen.add((b, b2, k))
                if b == b2:
                    # iota: (P0, Q) -> (Q, P0) ~ (P0, g^-1 P0) where Q = g P0
                    g = C.rep[b2][kq]
                    kq2 = C.coset_of[b][inv(g)]
                    for s in stabP:
                        seen.add((b, b2, C.act(s, b2, kq2)[0]))
                # local group
                gens = []
                for s in stabP:
                    k2, jq = C.act(s, b2, kq)
                    if k2 == kq and s != ident:
                        _, jp = C.act(s, b, 0)
                        gens.append(m_norm(("d", Fr(jp, C.e[b]), Fr(jq, C.e[b2]))))
                if b == b2:
                    # (sigma, iota): sigma Q = P0 and sigma P0 = Q
                    g = C.rep[b2][kq]
                    for sigma in (mul(g, t) for t in stabP):  # sigma P0 = Q
                        kP, jP = C.act(sigma, b, 0)          # sigma P0
                        if kP != kq:
                            continue
                        kQ, jQ = C.act(sigma, b2, kq)        # sigma Q
                        if kQ != 0:
                            continue
                        # matrix [[0, der(sigma, Q)], [der(sigma, P), 0]]
                        gens.append(m_norm(("a", Fr(jQ, C.e[b2]), Fr(jP, C.e[b]))))
                if not gens:
                    continue
                H = closure(gens)
                out.append(((b, b2, kq), H))
    return out


def analyse(name, t0, tinf, d):
    trip = find_triples(t0, tinf, d)
    print("== %s: d = %d, %d admissible transpositions for canonical s_inf" % (name, d, len(trip)))
    C = Cover(trip[0], d)
    inv_ = global_invariants(C)
    print("   genus(C^) = %d   p_g(W_2) = %d   p_g(Z) = %d   q = 0" % (inv_["g"], inv_["pg_W"], inv_["pg_Z"]))
    print("   e(W_2) = %s   K_W^2 = %s   (Z = X/S_d: e = %s, K^2 = %s)"
          % (inv_["eW"], inv_["K2W"], inv_["eZ"], inv_["K2Z"]))
    pts = singular_points(C)
    sum_r, sum_delta = 0, Fr(0)
    types = {}
    for key, H in pts:
        Hp = remove_reflections(H)
        N, q = cyclic_type(Hp)
        r, delta = delta_and_r(N, q)
        sum_r += r
        sum_delta += delta
        lab = "smooth" if N == 1 else "1/%d(1,%d)" % (N, q)
        types[(len(H), lab)] = types.get((len(H), lab), 0) + 1
    print("   special points (|H|, type after reflections): %s" % dict(sorted(types.items(), key=str)))
    chi = 1 + inv_["pg_W"]
    eS = inv_["eW"] + sum_r
    K2_noether = 12 * chi - eS
    K2_local = inv_["K2W"] - sum_delta
    print("   chi(O_S) = %d   e(S) = %s   K_S^2: Noether %s, local %s  -> %s"
          % (chi, eS, K2_noether, K2_local, "AGREE" if K2_noether == K2_local else "DISAGREE"))
    gt = K2_noether == K2_local and K2_noether > 0 and inv_["pg_W"] >= 1
    print("   general type: %s" % ("yes (K_S^2 > 0, p_g >= 1)" if gt else "not shown"))
    return dict(inv_, K2S=K2_noether, K2_local=K2_local, eS=eS, gt=gt, types=types)


if __name__ == "__main__":
    cases = [
        ("pp(2,1)  [d=3 control]", (2, 1), (3,), 3),
        ("pp(3,1) = tri(4) [d=4 control]", (3, 1), (4,), 4),
        ("tri(5) = pp(4,1)", (4, 1), (5,), 5),
        ("pp(3,2)", (3, 2), (5,), 5),
        ("tri(6) = pp(5,1)", (5, 1), (6,), 6),
        ("pp(4,3)", (4, 3), (7,), 7),
    ]
    if sys.argv[1:2] == ["pp"]:
        # python3 F1_kodaira.py pp p q   -> any coprime pp(p, q)
        p, q = int(sys.argv[2]), int(sys.argv[3])
        analyse("pp(%d,%d)" % (p, q), (p, q), (p + q,), p + q)
        sys.exit(0)
    which = sys.argv[1:] or [c[0] for c in cases]
    for name, t0, tinf, d in cases:
        if name in which or any(w in name for w in which):
            analyse(name, t0, tinf, d)
