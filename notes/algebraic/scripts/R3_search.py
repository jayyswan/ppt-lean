"""R3: search for simultaneous squares via V_tau.

Exact arithmetic over Q.  A number field K = Q[x]/(q) is represented by
coefficient vectors in the basis 1, b, ..., b^(n-1).

V_tau = {rho in K : rho^2 in span_Q{1, tau, tau^2}}.
Each rho in V_tau off the line span{1,tau} gives a binary form
    Q(s) = c s^2 - b s + a,   where rho^2 = a + b tau + c tau^2,
and Q(tau) = rho^2 is a square in K by construction.

Usage:
    py -3 R3_search.py n5        positive control (Y1a quintic)
    py -3 R3_search.py n5own     same field, V_tau search only
    py -3 R3_search.py n6        warm-up
    py -3 R3_search.py n7        main search
"""

import sys
import itertools
from fractions import Fraction

import numpy as np

# ----------------------------------------------------------------------------
# number field arithmetic
# ----------------------------------------------------------------------------


class NF:
    def __init__(self, coeffs_low_to_high):
        # monic q = x^n + c_{n-1} x^{n-1} + ... + c_0
        assert coeffs_low_to_high[-1] == 1
        self.q = [int(c) for c in coeffs_low_to_high]
        self.n = len(self.q) - 1
        self._build_mult_tables()

    def _build_mult_tables(self):
        """mult[k][i][j] = coefficient of b^k in b^i * b^j mod q (integers)."""
        n, q = self.n, self.q
        mult = [[[0] * n for _ in range(n)] for _ in range(n)]
        for i in range(n):
            for j in range(n):
                # product x^(i+j), reduce
                poly = [0] * (2 * n)
                poly[i + j] = 1
                for k in range(2 * n - 1, n - 1, -1):
                    c = poly[k]
                    if c:
                        poly[k] = 0
                        for t in range(n):
                            poly[k - n + t] -= c * q[t]
                for k in range(n):
                    mult[k][i][j] = poly[k]
        self.mult = mult

    def mul(self, a, b):
        n = self.n
        out = [0] * n
        for i in range(n):
            if a[i]:
                ai = a[i]
                for j in range(n):
                    if b[j]:
                        bj = b[j]
                        for k in range(n):
                            out[k] += ai * bj * self.mult[k][i][j]
        return out

    def square(self, a):
        return self.mul(a, a)

    def form_coords(self, rho, tau):
        """Solve rho^2 = a + b tau + c tau^2; return (a,b,c) as Fractions or None."""
        rhs = self.square(rho)
        # unknowns a,b,c ; equations: a*1 + b*tau + c*tau^2 = rhs in Q^n
        cols = [[Fraction(x) for x in v] for v in (self.one(), tau, self.square(tau))]
        # Gaussian elimination on the n x 3 system
        m = [row[:] for row in zip(*cols)]  # n rows, 3 cols
        r = [Fraction(x) for x in rhs]
        n = self.n
        piv = []
        row = 0
        for col in range(3):
            p = None
            for i in range(row, n):
                if m[i][col] != 0:
                    p = i
                    break
            if p is None:
                continue
            m[row], m[p] = m[p], m[row]
            r[row], r[p] = r[p], r[row]
            pv = m[row][col]
            m[row] = [x / pv for x in m[row]]
            r[row] = r[row] / pv
            for i in range(n):
                if i != row and m[i][col] != 0:
                    f = m[i][col]
                    m[i] = [m[i][k] - f * m[row][k] for k in range(3)]
                    r[i] = r[i] - f * r[row]
            piv.append(col)
            row += 1
            if row == n:
                break
        # consistency
        for i in range(row, n):
            if any(m[i][k] != 0 for k in range(3)):
                return None
            if r[i] != 0:
                return None
        sol = [Fraction(0), Fraction(0), Fraction(0)]
        for i, col in enumerate(piv):
            sol[col] = r[i]
        return tuple(sol)

    def one(self):
        v = [0] * self.n
        v[0] = 1
        return v

    def sym_pow(self, v, e):
        return self.mul(v, v) if e == 2 else v


def mat_rank(rows):
    m = [[Fraction(x) for x in row] for row in rows]
    if not m:
        return 0
    nr, nc = len(m), len(m[0])
    r = 0
    for c in range(nc):
        p = None
        for i in range(r, nr):
            if m[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(nr):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [m[i][k] - f * m[r][k] for k in range(nc)]
        r += 1
        if r == nr:
            break
    return r


def kernel(rows, ncols):
    """Basis of the kernel of the matrix with given rows (over Q)."""
    m = [[Fraction(x) for x in row] for row in rows]
    piv = []
    r = 0
    nr = len(m)
    for c in range(ncols):
        p = None
        for i in range(r, nr):
            if m[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(nr):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [m[i][k] - f * m[r][k] for k in range(ncols)]
        piv.append(c)
        r += 1
        if r == nr:
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for f in free:
        v = [Fraction(0)] * ncols
        v[f] = Fraction(1)
        for i, c in enumerate(piv):
            v[c] = -m[i][f]
        basis.append(v)
    return basis


def nullspace_int(rows, ncols):
    """Integer basis of the kernel (Fraction-free scaling)."""
    bas = kernel(rows, ncols)
    out = []
    for v in bas:
        den = 1
        for x in v:
            den = den * x.denominator // _gcd(den, x.denominator)
        out.append([int(x * den) for x in v])
    return out


def _gcd(a, b):
    while b:
        a, b = b, a % b
    return abs(a)


# ----------------------------------------------------------------------------
# V_tau search
# ----------------------------------------------------------------------------


def quotient_rows(F, tau):
    """Rows of an integer matrix R with R x = 0 iff x in span{1,tau,tau^2}."""
    n = F.n
    W = [F.one(), list(tau), F.square(tau)]
    # row space basis of W with pivots
    rows = [[Fraction(x) for x in w] for w in W]
    piv = []
    r = 0
    for c in range(n):
        p = None
        for i in range(r, len(rows)):
            if rows[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        rows[r], rows[p] = rows[p], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [rows[i][k] - f * rows[r][k] for k in range(n)]
        piv.append(c)
        r += 1
    # now rows[:r] has pivots piv
    R = []
    for j in range(n):
        if j in piv:
            continue
        # vector e_j - sum c_i rows[i] with zero pivot coordinates
        v = [Fraction(0)] * n
        v[j] = Fraction(1)
        coeffs = []
        for i, c in enumerate(piv):
            coeffs.append(rows[i][j])
        for i, c in enumerate(piv):
            ci = coeffs[i]
            if ci != 0:
                for k in range(n):
                    v[k] -= ci * rows[i][k]
        R.append(v)
    # clear denominators
    Rint = []
    for v in R:
        den = 1
        for x in v:
            den = den * x.denominator // _gcd(den, x.denominator)
        Rint.append([int(x * den) for x in v])
    return Rint


def quad_forms(F, R):
    """B_l (symmetric integer matrices) with condition R rho^2 = 0 iff rho in W."""
    n = F.n
    Bs = []
    for l in range(len(R)):
        B = [[0] * n for _ in range(n)]
        for k in range(n):
            if R[l][k] == 0:
                continue
            for i in range(n):
                for j in range(n):
                    B[i][j] += R[l][k] * F.mult[k][i][j]
        # symmetrise (mult is symmetric anyway)
        Bs.append(B)
    return Bs


def eval_quads(Bs, V):
    """V: (N,n) int64 array.  Returns (N,m) values of the quadratic forms."""
    N, n = V.shape
    out = np.zeros((N, len(Bs)), dtype=np.int64)
    for l, B in enumerate(Bs):
        B = np.asarray(B, dtype=np.int64)
        # x^T B x via einsum
        tmp = V @ B  # (N,n)
        out[:, l] = np.einsum("ij,ij->i", tmp, V)
    return out


def enumerate_V(F, tau, H, chunk=2_000_000):
    """Enumerate rho in [-H,H]^n with rho^2 in W_tau.  Returns list of tuples."""
    n = F.n
    R = quotient_rows(F, tau)
    Bs = quad_forms(F, R)
    sols = []
    total = (2 * H + 1) ** n
    # iterate in chunks over the first coordinate
    grid = np.arange(-H, H + 1, dtype=np.int64)
    rest = np.stack(np.meshgrid(*([grid] * (n - 1)), indexing="ij"), axis=-1).reshape(-1, n - 1)
    for r0 in range(-H, H + 1):
        V = np.empty((rest.shape[0], n), dtype=np.int64)
        V[:, 0] = r0
        V[:, 1:] = rest
        Qv = eval_quads(Bs, V)
        mask = np.all(Qv == 0, axis=1)
        for row in V[mask]:
            sols.append(tuple(int(x) for x in row))
    return sols


# ----------------------------------------------------------------------------
# forms and positivity
# ----------------------------------------------------------------------------


def rho_to_form(F, tau, rho):
    abc = F.form_coords(rho, tau)
    if abc is None:
        return None
    a, b, c = abc
    return (a, b, c)


def is_pos_def(abc, tau_is_real=True):
    a, b, c = abc
    if c <= 0:
        return False
    return 4 * c * a - b * b > 0


def normalize_form(abc):
    a, b, c = abc
    # scale so that c = 1
    if c == 0:
        return None
    return (a / c, b / c, Fraction(1))


def dedupe_forms(forms):
    out = {}
    for abc in forms:
        if abc is None:
            continue
        na = normalize_form(abc)
        if na is None:
            continue
        key = (na[0], na[1])
        out[key] = na
    return list(out.values())


# ----------------------------------------------------------------------------
# tests
# ----------------------------------------------------------------------------

Q5 = [Fraction(-1), Fraction(4), Fraction(0), Fraction(-5), Fraction(0), Fraction(1)]
Q6 = [Fraction(721), Fraction(-1764), Fraction(1624), Fraction(-735), Fraction(175), Fraction(-21), Fraction(1)]
Q7 = [Fraction(-5039), Fraction(13068), Fraction(-13132), Fraction(6769), Fraction(-1960), Fraction(322), Fraction(-28), Fraction(1)]


def run(field_coeffs, tau_expr, H, label):
    F = NF([int(x) for x in field_coeffs])
    tau = tau_expr(F)
    sols = enumerate_V(F, tau, H)
    forms = []
    for rho in sols:
        abc = rho_to_form(F, tau, rho)
        if abc is None:
            continue
        if is_pos_def(abc):
            forms.append(abc)
    forms = dedupe_forms(forms)
    print(f"[{label}] H={H}: {len(sols)} cone solutions, {len(forms)} positive-definite forms up to scaling")
    for f in forms[:20]:
        print("   ", tuple(str(x) for x in f))
    return F, tau, forms


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "n5"
    if mode == "n5":
        F, tau, forms = run(Q5, lambda F: [0, 1, 0, 0, 0], 3, "n5 tau=beta")
    elif mode == "n6":
        F, tau, forms = run(Q6, lambda F: [0, 1, 0, 0, 0, 0], 3, "n6 tau=beta")
    elif mode == "n7":
        F, tau, forms = run(Q7, lambda F: [0, 1, 0, 0, 0, 0, 0], 2, "n7 tau=beta")


if __name__ == "__main__":
    main()
