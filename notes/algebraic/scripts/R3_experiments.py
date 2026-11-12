"""R3 experiment driver: classification of V_tau points and the Theorem R read-out.

Conventions.
  K = Q[x]/(q), basis 1, b, ..., b^(n-1).
  tau in K.  W_tau = span_Q{1, tau, tau^2}.
  rho in V_tau iff rho^2 = a + b tau + c tau^2 with a,b,c in Q.
  The associated binary form is  Q(s) = c s^2 + b s + a = b11 s^2 - 2 b12 s + b22,
  so b11 = c, b12 = -b/2, b22 = a.
  Q is positive definite iff c > 0 and 4ac - b^2 > 0.
"""

import sys
from fractions import Fraction

import numpy as np

sys.path.insert(0, "notes/algebraic/scripts")
from R3_search import NF, quotient_rows, quad_forms, eval_quads, kernel, Q5, Q6, Q7


def classify(F, tau, H, max_sols=None):
    """Enumerate primitive rho in [-H,H]^n on V_tau, classified up to sign and scaling."""
    n = F.n
    R = quotient_rows(F, tau)
    Bs = quad_forms(F, R)
    grid = np.arange(-H, H + 1, dtype=np.int64)
    rest = np.stack(np.meshgrid(*([grid] * (n - 1)), indexing="ij"), axis=-1).reshape(-1, n - 1)
    seen = set()
    recs = []
    for r0 in range(0, H + 1):
        V = np.empty((rest.shape[0], n), dtype=np.int64)
        V[:, 0] = r0
        V[:, 1:] = rest
        # primitive and canonical sign (first nonzero coordinate > 0)
        g = np.gcd.reduce(np.abs(V), axis=1)
        prim = g == 1
        first = np.argmax(V != 0, axis=1)
        signok = V[np.arange(V.shape[0]), first] > 0
        keep = prim & signok
        V = V[keep]
        if V.shape[0] == 0:
            continue
        Qv = eval_quads(Bs, V)
        V = V[np.all(Qv == 0, axis=1)]
        for row in V:
            key = tuple(int(x) for x in row)
            if key in seen:
                continue
            seen.add(key)
            abc = F.form_coords([Fraction(x) for x in key], [Fraction(x) for x in tau])
            if abc is None:
                continue
            a, b, c = abc
            det = 4 * c * a - b * b
            if c == 0:
                kind = "lin"
            elif det == 0:
                kind = "deg"
            elif c > 0 and det > 0:
                kind = "pd"
            elif c < 0 and det > 0:
                kind = "nd"
            else:
                kind = "ind"
            recs.append((key, abc, det, kind))
            if max_sols and len(recs) >= max_sols:
                return recs
    return recs


def report(F, tau, H, label):
    recs = classify(F, tau, H)
    counts = {}
    for _, _, _, k in recs:
        counts[k] = counts.get(k, 0) + 1
    print(f"[{label}] H={H}: total {len(recs)}  {counts}")
    pds = []
    for key, abc, det, k in recs:
        if k == "pd":
            a, b, c = abc
            pds.append((a, b, c, key))
    # dedupe up to homothety: normalize c = 1
    uniq = {}
    for a, b, c, key in pds:
        uniq[(a / c, b / c)] = (a, b, c, key)
    print(f"   positive-definite forms up to homothety: {len(uniq)}")
    for k, (a, b, c, key) in list(uniq.items())[:12]:
        print(f"     Q = {c} s^2 + {b} s + {a}   [rho = {key}]")
    return recs, list(uniq.values())


def tau_spec(n, spec):
    """Coefficient vector of a tau in the power basis."""
    v = [0] * n
    if spec == "beta":
        v[1] = 1
    elif spec == "bp1":
        v[0] = 1
        v[1] = 1
    elif spec == "b2p1":
        v[0] = 1
        v[2] = 1
    elif spec == "2b":
        v[1] = 2
    elif spec == "3b":
        v[1] = 3
    else:
        raise SystemExit(f"unknown tau spec {spec}")
    return v


if __name__ == "__main__":
    mode = sys.argv[1]
    H = int(sys.argv[2])
    spec = sys.argv[3] if len(sys.argv) > 3 else "beta"
    Q = {"n5": Q5, "n6": Q6, "n7": Q7}[mode]
    F = NF([int(x) for x in Q])
    report(F, tau_spec(F.n, spec), H, f"{mode} {spec}")
