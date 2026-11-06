"""
B2-02b: Hermite trace form B(f,g)=Tr(fg) on A=R[x]/(q), exact.
Signature via Jacobi's theorem (signs of leading principal minors):
#negative = #sign changes in d_0=1,d_1,...,d_n (if all d_k != 0).
Checks: totally real => definite; one conjugate pair => indefinite on W.
"""
from sympy import symbols, Poly, Matrix, Rational

x = symbols('x')

def power_sums(p):
    """exact s_k = sum of k-th powers of roots, from Newton's identities (coefficients in Q)."""
    p = Poly(p, x)
    n = p.degree()
    cs = p.all_coeffs()               # [1, a_{n-1}, ..., a_0]
    a = [Rational(cs[n-k]) for k in range(n)]   # a[k] = coeff of x^{n-k}? recompute
    # elementary symmetric e_k from coefficients: p = x^n - e1 x^{n-1} + e2 x^{n-2} - ...
    # so a_{n-k}=(-1)^k e_k  -> e_k = (-1)^k * coeff_{n-k}
    e = [Rational(1)]
    for k in range(1, n+1):
        e.append((-1)**k * Rational(p.all_coeffs()[k]))
    s = [Rational(0)]*(2*n+1)
    for k in range(1, 2*n+1):
        if k <= n:
            s[k] = e[k] if k == 1 else 0
        # use Newton: k e_k = sum_{i=1}^k (-1)^{i-1} e_{k-i} s_i
    # compute s_k iteratively via Newton's identity
    S = [Rational(0)]*(2*n+1)
    for k in range(1, 2*n+1):
        acc = Rational(0)
        for i in range(1, k):
            if k-i <= n:
                acc += (-1)**(i-1)*e[k-i]*S[i]
        if k <= n:
            S[k] = ((-1)**(k-1)*k*e[k] - acc)/k if k > 0 else 0
            # Newton: s_k - e1 s_{k-1} + e2 s_{k-2} - ... + (-1)^{k-1} e_{k-1} s_1 + (-1)^k k e_k = 0
        else:
            S[k] = Rational(0)
    # recompute correctly using recurrence p_k = sum (-1)^{i-1} e_i p_{k-i}, with p_j=0 j<0, and
    # Newton: for k<=n: p_k - e1 p_{k-1} + ... + (-1)^{k-1} e_{k-1} p_1 + (-1)^k k e_k = 0
    P = [Rational(0)]*(2*n+1)
    for k in range(1, 2*n+1):
        acc = Rational(0)
        for i in range(1, min(k, n)+1):
            if k-i >= 1:
                acc += (-1)**(i-1)*e[i]*P[k-i]
        rhs = -acc
        if k <= n:
            rhs += (-1)**(k-1)*k*e[k]
        P[k] = rhs if k <= n else -acc
        # note for k>n, e_k=0 so recurrence p_k = sum_{i=1}^n (-1)^{i-1} e_i p_{k-i}
    return P

def signature_gram(G):
    n = G.shape[0]
    d = [Rational(1)]
    M = Matrix(G)
    for k in range(1, n+1):
        dk = M[:k, :k].det()
        d.append(dk)
    signs = [1 if v > 0 else (-1 if v < 0 else 0) for v in d]
    neg = sum(1 for i in range(1, len(signs)) if signs[i] != 0 and signs[i-1] != 0 and signs[i]*signs[i-1] < 0)
    zeros = sum(1 for v in signs if v == 0)
    return d, neg, zeros

def report(p, label):
    p = Poly(p, x)
    n = p.degree()
    P = power_sums(p)
    G = Matrix(n, n, lambda i, j: P[i+j] if (i+j) >= 1 else Rational(n))
    # B(x^i,x^j)=Tr(x^{i+j}); i+j=0 -> Tr(1)=n
    d, neg, zeros = signature_gram(G)
    print(f"{label}: deg {n}")
    print("  B signature (pos,neg) =", (n-neg, neg), " zeros:", zeros)
    print("  minors signs:", ['+' if v>0 else ('-' if v<0 else '0') for v in d])
    # Q|W : basis w_k = x^k - s_k/n, k=1..n-1, Q matrix = Tr(w_a w_b)
    s = P
    m = n-1
    def wc(k):
        c = [Rational(0)]*n
        c[k] = Rational(1)
        c[0] = -s[k]/n
        return c
    basis = [wc(k) for k in range(1, n)]
    QG = Matrix(m, m, lambda a, b: sum(basis[a][i]*basis[b][j]*(P[i+j] if i+j>=1 else n)
                                       for i in range(n) for j in range(n)))
    dq, negq, zerosq = signature_gram(QG)
    print("  Q on W signature (pos,neg) =", (m-negq, negq), " zeros:", zerosq)
    print()

tot = x**7 - 14*x**5 + 49*x**3 - 36*x + 1
quintic_real = (x-1)*(x-2)*(x-3)*(x-4)*(x-5)
one_pair = quintic_real*(x**2+1)
two_pair = (x-1)*(x-2)*(x-3)*(x**2+1)*(x**2+4)
report(tot, "totally real septic")
report(one_pair, "septic w/ one conjugate pair")
report(two_pair, "septic w/ two conjugate pairs")
