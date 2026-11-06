"""
B2-02: Hermite trace form B(f,g)=Tr(fg) on A=R[x]/(q): signature vs real-root
pattern, and its restriction to W={Tr f=0} (the p1=0 hyperplane).
Also checks the offset decic from Pptc/Offset.lean (l.748).
"""
from sympy import symbols, Poly, Matrix, Rational, nroots, eye, zeros, binomial
import numpy as np

x = symbols('x')

def companion(coeffs):
    # coeffs monic, highest first, length n+1
    n = len(coeffs) - 1
    M = zeros(n, n)
    for i in range(1, n):
        M[i, i-1] = 1
    for i in range(n):
        M[i, n-1] = -coeffs[n-i]  # constant..x^{n-1} -> careful
    return M

def companion_poly(p):
    p = Poly(p, x)
    n = p.degree()
    cs = p.all_coeffs()  # monic assumed
    M = np.zeros((n, n))
    for i in range(1, n):
        M[i, i-1] = 1.0
    for i in range(n):
        M[i, n-1] = -float(cs[n-i])
    return M

def trace_form_signature(p):
    p = Poly(p, x)
    n = p.degree()
    M = companion_poly(p)
    # trace power sums s_k = tr(M^k)
    def s(k):
        Mk = np.linalg.matrix_power(M, k)
        return np.trace(Mk)
    # Gram of B on basis 1,x,...,x^{n-1}: B_{ij} = s_{i+j}
    B = np.array([[s(i+j) for j in range(n)] for i in range(n)])
    ev = np.linalg.eigvalsh(B)
    pos = int(np.sum(ev > 1e-6*np.max(np.abs(ev))))
    neg = int(np.sum(ev < -1e-6*np.max(np.abs(ev))))
    return pos, neg, ev

def signature_on_W(p):
    """restrict Q(f)=Tr(f^2) to W={Tr f=0} = span{x^i - s_i/7}."""
    p = Poly(p, x)
    n = p.degree()
    M = companion_poly(p)
    def s(k):
        return np.trace(np.linalg.matrix_power(M, k))
    # basis w_k = x^k - s_k/7, k=1..n-1 ; coordinates f_k, constant = -s_k/7
    basis = []
    for k in range(1, n):
        c = np.zeros(n)       # coefficients of x^0..x^{n-1}
        c[k] += 1.0
        c[0] += -s(k)/n
        basis.append(c)
    m = n-1
    Q = np.zeros((m, m))
    for a in range(m):
        for b in range(m):
            # Tr(w_a w_b) = sum over polys of coefficients: use s_{i+j}
            val = 0.0
            for i in range(n):
                for j in range(n):
                    val += basis[a][i]*basis[b][j]*s(i+j)
            Q[a, b] = val
    ev = np.linalg.eigvalsh(Q)
    scale = max(abs(ev.max()), abs(ev.min()))
    pos = int(np.sum(ev > 1e-6*scale))
    neg = int(np.sum(ev < -1e-6*scale))
    return pos, neg

totally_real = x**7 - 14*x**5 + 49*x**3 - 36*x + 1
# a septic with one conjugate pair: (x^2+1)*cubic with 5 real roots? simpler: quintic real * (x^2+1)
quintic_real = (x-1)*(x-2)*(x-3)*(x-4)*(x-5)
one_pair = quintic_real*(x**2+1)
print("totally real septic  :", totally_real)
print("  B signature (A) : dim W=6:",
      trace_form_signature(totally_real)[:2], " Q|W:", signature_on_W(totally_real))
print("  numeric roots real?:",
      int(np.sum(np.abs(nroots(totally_real, n=30)) )))
print()
print("one-pair septic (5 real + 1 pair):", one_pair)
print("  B signature (A):", trace_form_signature(one_pair)[:2],
      " Q|W:", signature_on_W(one_pair))
print()

offset_decic = (10*x**10 - 30*x**9 + 89*x**8 - 114*x**7 + 152*x**6 - 58*x**5
                + 38*x**4 + 30*x**3 - 16*x**2 - 2)
r = nroots(offset_decic, n=30)
print("offset decic real roots:", [complex(v) for v in r if abs(complex(v).imag) < 1e-12])
print("offset decic factor mod 29:", Poly(offset_decic, x).factor_list(modulus=29) if False else "(see Offset.lean)")
