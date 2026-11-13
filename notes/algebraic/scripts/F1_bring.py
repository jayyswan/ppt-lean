"""F1 stage B: Bring-Jerrard for quintic fields, as a positive control for the
forward-search pipeline and as a calibration of the sizes of (L, lambda).

For K = Q(beta), f monic quintic:
  y = a0 + a1 b + a2 b^2 + a3 b^3 + a4 b^4,   Tr y = 0 fixes a0;
  Q(a) = Tr y^2 (quadratic form), C(a) = Tr y^3 (cubic form) in a1..a4.
  1. a point P on Q = 0: rational if a box search finds one, else
     P = e_i + t e_j with t quadratic;
  2. the lines on Q through P lie in the tangent plane: V with v_m = 0,
     v_n = 1, v_k solved from B(P, V) = 0, the fourth coordinate r a root of
     the quadratic Q(V) = 0;
  3. on the line a = s P + V, C(a) = 0 is a cubic in s.
  Then the char. poly of y over L = Q(t, r, s) is y^5 + A y + B with
  A = -Tr(y^4)/4, B = -Tr(y^5)/5 (Newton, e1 = e2 = e3 = 0), and y = c x with
  c = -B/A turns it into x^5 + lam x - lam, lam = A^5/B^4: the tri(5) engine.
  4. h = minimal polynomial of lam: successive resultants over the relations
     for s, r, t, factored over Q; the factor holding our lam is picked by
     ball arithmetic.
Then filter_h, certify (blind: it must return a field isomorphic to K), and
the independent Trager check has_root_in(f, N_h).

Usage: python3 F1_bring.py [count]       (Windows: py -3 F1_bring.py)
"""

import itertools
import sys
import time
from fractions import Fraction as Fr

from flint import (acb, ctx, fmpq, fmpq_mpoly_ctx, fmpz_poly, fmpq_poly)

sys.path.insert(0, ".")
from F1_core import (TableCache, certify, fields_isomorphic, filter_h,  # noqa: E402
                     galois_certificate, has_root_in, N_of, signature, tri,
                     roots_balls, is_squarefree, _balls_disjoint)

VARS = ("a1", "a2", "a3", "a4", "t", "r", "s", "L")
R = fmpq_mpoly_ctx.get(VARS, "lex")
a1, a2, a3, a4, tv, rv, sv, Lv = R.gens()
AV = [a1, a2, a3, a4]


def RC(x):
    return R.constant(x)

# ----------------------------------------------------------------------------
# quintic field arithmetic over the polynomial ring R
# ----------------------------------------------------------------------------


def power_traces(f, kmax=12):
    """Tr(beta^k), k = 0..kmax, for monic integer f (Newton)."""
    c = [Fr(int(x)) for x in f.coeffs()]  # low to high, c[5] = 1
    n = 5
    e = [Fr(1)] + [(-1) ** k * c[n - k] for k in range(1, n + 1)]
    p = [Fr(n)]
    for k in range(1, kmax + 1):
        s = Fr(0)
        for i in range(1, min(k, n) + 1):
            if i < k:
                s += (-1) ** (i - 1) * e[i] * p[k - i]
        if k <= n:
            s += (-1) ** (k - 1) * k * e[k]
        p.append(s)
    return p


def mulmod(u, v, f):
    """Product of two elements (lists of 5 coefficients in R) of R[b]/f."""
    c = [int(x) for x in f.coeffs()]
    prod = [RC(0)] * 9
    for i in range(5):
        if u[i] == 0:
            continue
        for j in range(5):
            if v[j] != 0:
                prod[i + j] += u[i] * v[j]
    for k in range(8, 4, -1):  # b^k = b^(k-5) * b^5, b^5 = -sum c_i b^i
        if prod[k] == 0:
            continue
        coef = prod[k]
        prod[k] = RC(0)
        for i in range(5):
            if c[i]:
                prod[k - 5 + i] -= coef * c[i]
    return prod[:5]


def trace(u, tr):
    return sum((u[i] * fmpq(tr[i].numerator, tr[i].denominator) for i in range(5)), RC(0))


def forms(f):
    tr = power_traces(f)
    a0 = -sum((AV[i] * fmpq(tr[i + 1].numerator, tr[i + 1].denominator) for i in range(4)), RC(0)) / 5
    y = [a0] + AV
    pw = [None, y]
    for k in range(2, 6):
        pw.append(mulmod(pw[-1], y, f))
    T = [None] + [trace(pw[k], tr) for k in range(1, 6)]
    assert T[1] == 0
    return T[2], T[3], T[4], T[5]


def ev(F, vec):
    """Substitute a1..a4 -> vec (elements of R) into F."""
    return F.compose(*vec, tv, rv, sv, Lv)


# ----------------------------------------------------------------------------
# the construction
# ----------------------------------------------------------------------------


_POINT_CACHE = {}


def rational_point(Q, box):
    """Smallest-height nonzero integer zero of the quadratic form Q in the
    box, found from its Gram matrix (exact rational arithmetic)."""
    key = (str(Q), box)
    if key in _POINT_CACHE:
        return _POINT_CACHE[key]
    d = Q.to_dict()
    M = [[Fr(0)] * 4 for _ in range(4)]
    for k, c in d.items():
        idx = [i for i in range(4) for _ in range(k[i])]
        assert len(idx) == 2 and sum(k[4:]) == 0
        i, j = idx
        val = Fr(int(c.p), int(c.q))
        if i == j:
            M[i][i] += val
        else:
            M[i][j] += val / 2
            M[j][i] += val / 2
    den = 1
    for row in M:
        for x in row:
            den = den * x.denominator // __import__("math").gcd(den, x.denominator)
    Mi = [[int(x * den) for x in row] for row in M]
    best = None
    for hgt in range(1, box + 1):
        for v in itertools.product(range(-hgt, hgt + 1), repeat=4):
            if max(abs(x) for x in v) != hgt:
                continue
            if sum(Mi[i][j] * v[i] * v[j] for i in range(4) for j in range(4)) == 0:
                best = v
                break
        if best is not None:
            break
    _POINT_CACHE[key] = best
    return best


def grad_at(Q, P):
    return [Q.derivative(VARS[i]).compose(*P, tv, rv, sv, Lv) for i in range(4)]


def construct(f, box=4, choice=0):
    """Returns dict with lam relations: list of (var, poly) to eliminate,
    the final expression E(L) and the meta-data; `choice` picks among the
    admissible coordinate patterns (to vary the result)."""
    Q, C, P4, P5 = forms(f)
    out = {"Q": Q}
    v = rational_point(Q, box)
    rels = []
    if v is not None:
        P = [RC(x) for x in v]
        out["point"] = ("rational", v)
    else:
        # P = e_i + t e_j, Q(P) = 0 quadratic in t
        found = False
        for i, j in itertools.permutations(range(4), 2):
            P = [RC(0)] * 4
            P[i] = RC(1)
            P[j] = tv
            q1 = ev(Q, P)
            if q1.degrees()[4] == 2:
                rels.append(("t", q1))
                out["point"] = ("quadratic", (i, j))
                found = True
                break
        assert found
    g = grad_at(Q, P)
    # choose indices k (solved), m (zeroed, P_m != 0), n (normalised), free = r
    pats = []
    for k, m, n in itertools.permutations(range(4), 3):
        if g[k] != 0 and P[m] != 0:
            pats.append((k, m, n))
    k, m, n = pats[choice % len(pats)]
    free = [i for i in range(4) if i not in (k, m, n)][0]
    V = [RC(0)] * 4
    V[n] = RC(1)
    V[free] = rv
    V[m] = RC(0)
    # B(P, V) = sum g_i V_i = 0  ->  V_k = -(g_n + g_free r)/g_k
    num = -(g[n] * V[n] + g[free] * V[free])
    V[k] = None
    # avoid division: scale V by g_k
    V = [x * g[k] if x is not None else num for x in V]
    q2 = ev(Q, V)
    # q2 may carry the factor from t; it must be quadratic in r
    rels.append(("r", q2))
    line = [sv * P[i] + V[i] for i in range(4)]
    cub = ev(C, line)
    rels.append(("s", cub))
    A = -ev(P4, line) / 4
    B = -ev(P5, line) / 5
    E = Lv * B**4 - A**5
    out.update(rels=rels, A=A, B=B, E=E, pattern=(k, m, n, free), line=line)
    return out


def eliminate(out):
    E = out["E"]
    for var, rel in reversed(out["rels"]):
        E = rel.resultant(E, var)
    # univariate in L
    d = E.to_dict()
    deg = max(k[7] for k in d)
    co = [fmpq(0)] * (deg + 1)
    for k, val in d.items():
        assert sum(k[:7]) == 0
        co[k[7]] = val
    P = fmpq_poly(co)
    return P


def numeric_choice(out, prec=256):
    """Pick numeric values for t, r, s (real when possible) and return lam,
    and whether every chosen root was real."""
    old = ctx.prec
    ctx.prec = prec
    vals = {}
    allreal = True
    try:
        for var, rel in out["rels"]:
            # substitute known values, get univariate poly in var
            sub = rel
            idx = VARS.index(var)
            # build univariate by evaluating other variables numerically: do it
            # via the dict
            d = sub.to_dict()
            deg = max(kk[idx] for kk in d)
            co = [acb(0)] * (deg + 1)
            for kk, c in d.items():
                term = acb(c.p) / acb(c.q) if hasattr(c, "p") else acb(int(c))
                for vn, vval in vals.items():
                    term *= vval ** kk[VARS.index(vn)]
                co[kk[idx]] += term
            # roots via companion: use acb_poly
            from flint import acb_poly
            pol = acb_poly(co)
            rts = pol.roots()
            real = [z for z in rts if z.imag.contains(0) and abs(z.imag.mid()) < 1e-30]
            if real:
                pick = max(real, key=lambda z: -abs(z.real.mid()))
            else:
                allreal = False
                pick = rts[0]
            vals[var] = pick
        # lam
        def evalR(F):
            d = F.to_dict()
            acc = acb(0)
            for kk, c in d.items():
                term = acb(c.p) / acb(c.q)
                for vn, vval in vals.items():
                    term *= vval ** kk[VARS.index(vn)]
                acc += term
            return acc
        A = evalR(out["A"])
        B = evalR(out["B"])
        lam = A**5 / B**4
        return lam, allreal, A, B
    finally:
        ctx.prec = old


def pick_factor(P, lam):
    _, facs = P.factor()
    hits = []
    for g, e in facs:
        co = [int(x) for x in (g * g.denom()).numer().coeffs()] if hasattr(g, "numer") else None
        gz = fmpz_poly([int(x) for x in g.numer().coeffs()])
        val = acb(0)
        for c in reversed(gz.coeffs()):
            val = val * lam + acb(int(c))
        if val.contains(0):
            hits.append(gz)
    return hits


def height(h):
    return max(abs(int(c)) for c in h.coeffs())


# ----------------------------------------------------------------------------
# choosing the 20 quintic fields
# ----------------------------------------------------------------------------


def candidate_quintics(B=3):
    seen = []
    for c in itertools.product(range(-B, B + 1), repeat=5):
        f = fmpz_poly(list(c) + [1])
        if c[0] == 0:
            continue
        fac = f.factor()[1]
        if len(fac) != 1 or fac[0][0].degree() != 5:
            continue
        seen.append((abs(int(f.discriminant())), f))
    seen.sort(key=lambda x: x[0])
    return seen


def choose_fields(nS5=10, nA5=5, nTR=5, B=3):
    S5, A5, TR = [], [], []
    for D, f in candidate_quintics(B):
        sig = signature(f)
        grp = galois_certificate(f)
        if grp[1] != "proved":
            continue
        cls = None
        if sig == (5, 0):
            if len(TR) < nTR:
                cls = TR
        elif grp[0] == "A5":
            if len(A5) < nA5:
                cls = A5
        elif grp[0] == "S5":
            if len(S5) < nS5:
                cls = S5
        if cls is None:
            continue
        if any(fields_isomorphic(f, g) for _, g, _, _ in S5 + A5 + TR if g.degree() == 5 and _sqclass(D) == _sqclass(abs(int(g.discriminant())))):
            continue
        cls.append((D, f, sig, grp[0]))
        if len(S5) >= nS5 and len(A5) >= nA5 and len(TR) >= nTR:
            break
    return S5, A5, TR


def _sqclass(D):
    from flint import fmpz
    k = 2
    D = int(D)
    out = 1
    while k * k <= D:
        e = 0
        while D % k == 0:
            D //= k
            e += 1
        if e % 2:
            out *= k
        k += 1
    return out * D


if __name__ == "__main__":
    print("run via F1_bring_run.py")
