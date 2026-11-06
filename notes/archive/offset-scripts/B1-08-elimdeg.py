"""B1-08: elimination degree of the covering system over a finite field.

Degree of the Delta-elimination ideal is the same over F_p for almost all p.
Build W mod q, the 7 coefficient equations, and compute a lex Groebner basis
over F_p with Delta last.  Any basis element in Delta alone gives the degree.
"""
import sympy as sp
import sys, time

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)


def system(qcoeffs):
    q = sum(sp.Integer(int(co)) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    u = t ** 3 + a * t ** 2 + b * t + c
    up = sp.diff(u, t)
    vp = p * t ** 2 + qq * t + r
    W = sp.expand(u ** 2 * (up ** 2 + vp ** 2) - Dlt * vp ** 2)
    _, rem = sp.div(W, q, t)
    return [sp.expand(rem.coeff(t, i)) for i in range(7)]


def run(qcoeffs, prime=32003):
    eqs = system(qcoeffs)
    eqsp = [sp.Poly(e, *vars_, modulus=prime) for e in eqs]
    t0 = time.time()
    G = sp.groebner(eqsp, *vars_, order='lex', modulus=prime)
    dt = time.time() - t0
    print("q=", qcoeffs, " p=", prime, " groebner %.1fs" % dt, " basis size", len(G.polys))
    # elements involving only Delta
    onlyD = []
    for g in G.polys:
        mono = g.monoms()
        involved = set()
        for m in mono:
            for i, e in enumerate(m):
                if e > 0:
                    involved.add(i)
        if involved <= {6}:
            onlyD.append(sp.Poly(g, Dlt, modulus=prime))
    for pd in onlyD:
        print("   Delta-only poly, degree", pd.degree(), ":", pd.as_expr())
    return G, onlyD


if __name__ == '__main__':
    import ast
    qc = ast.literal_eval(sys.argv[1]) if len(sys.argv) > 1 else [1, 0, -14, 0, 49, 0, -36, 0]
    pr = int(sys.argv[2]) if len(sys.argv) > 2 else 32003
    run(qc, pr)
