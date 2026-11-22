# Session 61: row E with P dials in coefficient coordinates (exact, sympy).
# (1) family identity: chi_u * c = V(w^2) + R(w)  <=>  chi_u = quo(V(w^2), c) + t
# (2) good locus G and the T_6 fibre equations E6 (B3 = 0), E8 (4B4 = B2^2) as polynomials in a1..a8
# (3) planted check with S = T_6 (9 of the 12 crossings of a random member) and random controls
# Writes e61_formulas.pkl (Gn, E6, E8 as sympy expressions in a1..a9).
import sympy as sp, numpy as np, pickle

w, T = sp.symbols('w T')
a = sp.symbols('a1:10')            # chi_u = w^9 + a1 w^8 + ... + a9
c1, c2, c3 = sp.symbols('c1 c2 c3')
bb = sp.symbols('b1:5')

def formulas():
    A = [sp.Integer(1)] + list(a)
    C = [sp.Integer(1), c1, c2, c3]
    W = lambda k: sum(C[j]*A[k-j] for j in range(4) if 0 <= k-j <= 9)
    D = a[0]*a[1] - a[2]
    sol = sp.solve([W(1), W(3), W(5)], [c1, c2, c3], dict=True)[0]
    Gn = sp.expand(sp.cancel(W(7).subs(sol)*D))
    n = [sp.expand(sp.cancel(W(2*m).subs(sol)*D)) for m in (1, 2, 3, 4)]   # b_m = n_m / D
    V = T**6 + bb[0]*T**5 + bb[1]*T**4 + bb[2]*T**3 + bb[3]*T**2
    P = sp.Poly(sp.expand(V.subs(T, T - bb[0]/6)), T)
    B2, B3, B4 = [P.coeff_monomial(T**k) for k in (4, 3, 2)]
    # B3 is weighted-homogeneous of degree 3 in b (weights 1..4 -> total weight 3 in 1/D powers)
    sub = {bb[m]: n[m]/D for m in range(4)}
    E6 = sp.expand(sp.cancel(B3.subs(sub)*D**3))
    E8 = sp.expand(sp.cancel((4*B4 - B2**2).subs(sub)*D**4))
    return sol, Gn, n, (B2, B3, B4), E6, E8

if __name__ == '__main__':
    rng = np.random.default_rng(1)
    V = sp.Poly(sum(int(rng.integers(-9, 9))*w**(2*k) for k in range(6)) + w**12, w)
    cc = sp.Poly(w**3 + 2*w**2 - 3*w + 5, w)
    q, r = sp.div(V, cc)
    F = sp.expand((q.as_expr() + 7)*cc.as_expr())
    print('identity: deg(F - V(w^2)) =', sp.Poly(sp.expand(F - V.as_expr()), w).degree(), '(<= 3)')
    sol, Gn, n, Bs, E6, E8 = formulas()
    print('B2, B3, B4 in b:', Bs)
    print('G numerator:', Gn)
    print('E6 vars:', sorted(map(str, E6.free_symbols)), ' terms', len(E6.args), ' deg in a6:', sp.Poly(E6, a[5]).degree())
    print('E8 vars:', sorted(map(str, E8.free_symbols)), ' terms', len(E8.args), ' deg in a8:', sp.Poly(E8, a[7]).degree())
    cen = {a[0]: 0}
    print('centred G :', sp.factor(Gn.subs(cen)))
    print('centred E6:', sp.factor(E6.subs(cen)))
    pickle.dump((Gn, E6, E8), open('e61_formulas.pkl', 'wb'))
    fG = sp.lambdify([a], Gn); f6 = sp.lambdify([a], E6); f8 = sp.lambdify([a], E8)
    T6 = np.polynomial.chebyshev.cheb2poly([0]*6 + [1])
    for seed in range(3):
        rg = np.random.default_rng(10 + seed)
        al, be = 2 + 0.1*rg.standard_normal(), -1 + 0.1*rg.standard_normal()
        Y = 0.2*rg.standard_normal(4)
        N = np.polynomial.Polynomial(T6)(np.polynomial.Polynomial([be, 0, al])) - np.polynomial.Polynomial(Y)
        u = N.roots()[rg.permutation(12)[:9]]
        av = list(np.poly(u)[1:])
        u2 = rg.standard_normal(9) + 1j*rg.standard_normal(9); av2 = list(np.poly(u2)[1:])
        print(f'planted {seed}: |G|={abs(fG(av)):.1e} |E6|={abs(f6(av)):.1e} |E8|={abs(f8(av)):.1e};'
              f'  random: |G|={abs(fG(av2)):.1e} |E6|={abs(f6(av2)):.1e} |E8|={abs(f8(av2)):.1e}')
