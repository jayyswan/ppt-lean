# Session 14: invariants of degree d vanishing to order 4 along Pi whose normal quartic
# c1 (sum u^2)^2 + c2 sum u^4 (set 1) has ord_{a=b} c2 = k (even) and ord c1 >= k, near x8.
# Arithmetic mod p (p = 1 mod 4).  Pi is parametrised as (a,b) = (1+t, 1).
import random, sys
from ord4 import p, I, parts, nullspace
from math import comb
T = int(sys.argv[3]) if len(sys.argv) > 3 else 7    # t-precision
EPS = 5
def smul(A, B):
    C = [[0]*EPS for _ in range(T)]
    for i in range(T):
        for j in range(EPS):
            x = A[i][j]
            if x:
                for k in range(T-i):
                    Bk = B[k]
                    for l in range(EPS-j):
                        if Bk[l]: C[i+k][j+l] = (C[i+k][j+l] + x*Bk[l]) % p
    return C
def psums2(n):
    # x_j = base_j(t) + eps n_j ; base = (1+t)*4, 1*4, -4(2+t)
    base = [(1,1)]*4 + [(1,0)]*4 + [(-8,-4)]
    out = {}
    for k in range(2, 10):
        S = [[0]*EPS for _ in range(T)]
        for (c0, c1), nj in zip(base, n):
            # (c0 + c1 t + nj eps)^k
            for e in range(min(k, EPS-1)+1):
                ce = comb(k, e) * pow(nj, e, p) % p
                r = k - e
                for i in range(min(r, T-1)+1):
                    S[i][e] = (S[i][e] + ce * comb(r, i) * pow(c0, r-i, p) * pow(c1, i, p)) % p
        out[k] = S
    return out
def ev(lam, ps):
    S = [[1 if (i == 0 and j == 0) else 0 for j in range(EPS)] for i in range(T)]
    for k in lam: S = smul(S, ps[k])
    return S
def main(d, order):
    basis = list(parts(d)); nb = len(basis)
    # order-'order' along Pi: from random points and directions (as in ord4)
    from ord4 import run
    _, ns = run(d, order)
    ui = [1, I, p-1, p-I] + [0]*5
    um = [1, p-1, 1, p-1] + [0]*5
    Pi_ = psums2(ui); Pm = psums2(um)
    Eu = [ev(l, Pi_) for l in basis]; Em = [ev(l, Pm) for l in basis]
    rows_c2, rows_c1 = [], []
    for v in ns:
        qi = [sum(v[j]*Eu[j][i][order] for j in range(nb)) % p for i in range(T)]   # = 4 c2(t)
        qm = [sum(v[j]*Em[j][i][order] for j in range(nb)) % p for i in range(T)]   # = 16 c1 + 4 c2 (order 4) / 4 c1' (order 2)
        rows_c2.append(qi); rows_c1.append(qm)
    return ns, rows_c2, rows_c1
if __name__ == '__main__':
    d = int(sys.argv[1]); order = int(sys.argv[2])
    ns, C2, C1 = main(d, order)
    def ordt(r): return next((i for i, x in enumerate(r) if x), None)
    print('d', d, 'order', order, 'dim', len(ns))
    print(' ord_t of Q(u_i):', [ordt(r) for r in C2])
    print(' ord_t of Q(u_-1):', [ordt(r) for r in C1])
    # best k: combination with Q(u_i) = O(t^k), Q(u_-1) = O(t^k), and Q(u_i)_k != 0
    m = len(ns)
    for k in range(T):
        rows = [[C2[j][i] for j in range(m)] for i in range(k)] + [[C1[j][i] for j in range(m)] for i in range(k)]
        sol = nullspace(rows, m) if rows else [[1 if i == j else 0 for i in range(m)] for j in range(m)]
        good = [s for s in sol if sum(s[j]*C2[j][k] for j in range(m)) % p]
        print(' k=%d: solutions %d, with Q(u_i)_k != 0: %d' % (k, len(sol), len(good)))
