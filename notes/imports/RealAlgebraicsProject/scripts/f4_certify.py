# Exact: max of p4/p2^2 on real trace-zero vectors in R^9 is 19/24, attained only on L_j.
# Lagrange: 4x^3 - 2 mu x - nu = 0 at every coordinate, so <= 3 values; with 3 values the
# cubic has no x^2 term, so v1+v2+v3 = 0 (unweighted) and sum m_i v_i = 0.
import sympy as sp
from g6_certify import partitions
best = []
for k in (2, 3):
    for m in partitions(9, k):
        v = sp.symbols('v1:%d' % (k+1))
        rows = [list(m)] + ([[1]*k] if k == 3 else [])
        ns = sp.Matrix(rows).nullspace()
        if len(ns) == 2:   # (3,3,3): family (a, b, -a-b); ratio is constant
            a, b = sp.symbols('a b'); vals = [a, b, -a-b]
            P = lambda j: sum(mi*vi**j for mi, vi in zip(m, vals))
            r = sp.simplify(P(4)/P(2)**2); best.append((r, m)); print(m, 'family, ratio', r); continue
        vals = list(ns[0])
        if len(set(vals)) < k: print(m, 'degenerate', vals); continue
        P = lambda j: sum(mi*vi**j for mi, vi in zip(m, vals))
        r = sp.nsimplify(P(4)/P(2)**2)
        best.append((r, m)); print(m, vals, 'p4/p2^2 =', r, float(r))
print('max', max(best), ' 19/24 =', sp.Rational(19,24))
