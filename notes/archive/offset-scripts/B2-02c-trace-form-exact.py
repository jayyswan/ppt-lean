"""
B2-02c: Hermite trace form B(f,g)=Tr(fg) on A=R[x]/(q), exact via companion matrix.
Signature via Jacobi (signs of leading principal minors).
Checks: totally real => B definite (pos,n); one conjugate pair => Q|W indefinite.
"""
from sympy import symbols, Poly, Matrix, Rational

x = symbols('x')

def companion(p):
    p = Poly(p, x)
    n = p.degree()
    cs = p.all_coeffs()                       # [1, a_{n-1}, ..., a_0]
    C = Matrix.zeros(n, n)
    for i in range(1, n):
        C[i, i-1] = 1
    for i in range(n):
        C[i, n-1] = -Rational(cs[n-i])        # -a_i
    return C

def sig(G):
    n = G.shape[0]
    d = [Rational(1)]
    for k in range(1, n+1):
        d.append(G[:k, :k].det())
    sg = [1 if v > 0 else (-1 if v < 0 else 0) for v in d]
    neg = sum(1 for i in range(1, len(sg)) if sg[i] and sg[i-1] and sg[i]*sg[i-1] < 0)
    return (n-neg, neg, sum(1 for v in sg if v == 0)), sg

def report(p, label):
    p = Poly(p, x); n = p.degree(); C = companion(p)
    tr = lambda k: (C**k).trace() if k >= 1 else Rational(n)
    B = Matrix(n, n, lambda i, j: tr(i+j))
    sB, sgB = sig(B)
    print(f"{label}: deg {n}")
    print("  B = Tr(x^i x^j) signature (pos,neg) =", sB[:2], "zeros", sB[2])
    print("  minors signs:", ['+' if v > 0 else ('-' if v < 0 else '0') for v in sgB])
    # Q(f)=Tr(f^2) on W = {Tr f=0}, basis w_k = x^k - s_k/n, k=1..n-1
    s = lambda k: tr(k)
    m = n-1
    def wc(k):
        c = [Rational(0)]*n; c[k] = Rational(1); c[0] = -s(k)/n
        return c
    basis = [wc(k) for k in range(1, n)]
    Q = Matrix(m, m, lambda a, b: sum(basis[a][i]*basis[b][j]*s(i+j)
                                      for i in range(n) for j in range(n)))
    sQ, sgQ = sig(Q)
    print("  Q|W signature (pos,neg) =", sQ[:2], "zeros", sQ[2])
    print()

tot = x**7 - 14*x**5 + 49*x**3 - 36*x + 1
one_pair = (x-1)*(x-2)*(x-3)*(x-4)*(x-5)*(x**2+1)
two_pair = (x-1)*(x-2)*(x-3)*(x**2+1)*(x**2+4)
report(tot, "totally real septic (7 real)")
report(one_pair, "septic, 5 real + 1 pair")
report(two_pair, "septic, 3 real + 2 pairs")
