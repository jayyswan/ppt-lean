# Session 18: singular points of Q4 = 6 p4 - p2^2 on V = {sum z = 0} in P^7 (over C, coordinates = the 9 conjugates).
# At a singular point grad Q4 is proportional to (1,...,1): 24 z_i^3 - 4 p2 z_i = lam, so the z_i take at most 3 values,
# the roots alpha, beta, gamma of 24 z^3 - 4 p2 z - lam (sum 0, e2 = -p2/6). Euler's relation gives Q4 = 0 automatically.
# Enumerate multiplicity patterns (n1,n2,n3), n1+n2+n3 = 9 (n3 may be 0: the third root is then unused).
import sympy as sp
al, be = sp.symbols('alpha beta')
ga = -al - be
sols = []
for n1 in range(10):
    for n2 in range(10 - n1):
        n3 = 9 - n1 - n2
        if (n1, n2, n3) != tuple(sorted((n1, n2, n3), reverse=True)): continue
        lin = n1*al + n2*be + n3*ga
        p2 = n1*al**2 + n2*be**2 + n3*ga**2
        e2 = al*be + be*ga + ga*al
        eqs = [sp.expand(lin), sp.expand(6*e2 + p2)]
        # projective: set beta = 1 or alpha = 1
        found = []
        for chart in [(be, 1), (al, 1)]:
            E = [e.subs(*chart) for e in eqs]
            other = al if chart[0] == be else be
            if E[0] == 0 and E[1] == 0: found.append('all'); continue
            g = sp.gcd(sp.Poly(E[0], other), sp.Poly(E[1], other)) if E[0] != 0 else sp.Poly(E[1], other)
            for r in sp.roots(g if E[0] != 0 else sp.Poly(E[1], other)).keys():
                if E[0] == 0 or sp.simplify(E[0].subs(other, r)) == 0:
                    v = {chart[0]: chart[1], other: r}
                    a, b = v[al], v[be]; c = -a - b
                    vals = [a]*n1 + [b]*n2 + [c]*n3
                    if all(sp.simplify(x) == 0 for x in vals): continue
                    found.append(tuple(sp.nsimplify(x) for x in (a, b, c)))
        if found: sols.append(((n1, n2, n3), set(found)))
for s in sols: print(s)
