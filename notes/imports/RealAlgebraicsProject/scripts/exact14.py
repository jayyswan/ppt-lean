# Session 14, exact: normal forms along Pi of r9 (order 2) and R14 (order 4), factored in (a,b).
import pickle, sympy as sp, sys
r = pickle.load(open('radicands13.pkl','rb'))
P = sp.symbols('p2:10'); a, b, e = sp.symbols('a b e')
I = sp.I
def nf(f, n, order):
    x = [a]*4 + [b]*4 + [-4*(a+b)]
    sub = {}
    for k in range(2, 10):
        s = 0
        for xi, ni in zip(x, n):
            s += sum(sp.binomial(k, j)*xi**(k-j)*(ni*e)**j for j in range(order+1))
        sub[P[k-2]] = sp.expand(s)
    g = sp.Poly(f, *P)
    tot = 0
    for mon, c in g.terms():
        t = sp.Integer(c)
        for k, ex in enumerate(mon):
            for _ in range(ex):
                t = sp.expand(t*sub[P[k]]); t = sum(t.coeff(e, j)*e**j for j in range(order+1))
        tot += t
    tot = sp.expand(tot)
    low = [sp.simplify(tot.coeff(e, j)) for j in range(order)]
    assert all(l == 0 for l in low), 'not vanishing to order %d' % order
    return sp.factor(sp.expand(tot.coeff(e, order)))
um1 = [1,-1,1,-1,0,0,0,0,0]; ui1 = [1,I,-1,-I,0,0,0,0,0]
um2 = [0,0,0,0,1,-1,1,-1,0]; ui2 = [0,0,0,0,1,I,-1,-I,0]
which = sys.argv[1]
if which == 'r9':
    f = sp.sympify(r['r9'])
    print('r9 at u_-1 set1:', nf(f, um1, 2)); print('r9 at u_-1 set2:', nf(f, um2, 2))
else:
    f = sp.sympify(r['R14'])
    A = nf(f, ui1, 4); B = nf(f, um1, 4)
    c2 = sp.factor(A/4); c1 = sp.factor((B - A)/16)
    print('R14 c2 (set 1):', c2); print('R14 c1 (set 1):', c1)
    A2 = nf(f, ui2, 4); print('R14 Q(u_i) set 2:', A2)
