"""B1-13: bounded square analogue of the septic covering system.

Use a QUADRATIC pair (parabola) instead of a cubic pair: W = u^2(u'^2+v'^2) - D v'^2
has degree 6.  Cover a QUINTIC q: unknowns u monic quadratic (a,b), v' linear (p,r),
D = (a,b,p,r,Dlt) = 5; equations W mod q = 0 = 5.  Square, same shape as the septic
problem with (m,n) = (2,5) instead of (3,7).  Exact Groebner over F_p is bounded here.
"""
import sympy as sp
import numpy as np
import time, sys

t, a, b, p, r, Dlt = sp.symbols('t a b p r Delta')
vars_ = (a, b, p, r, Dlt)


def system(qcoeffs, mode='quadratic'):
    n = len(qcoeffs) - 1
    q = sum(sp.Integer(int(co)) * t ** (n - i) for i, co in enumerate(qcoeffs))
    if mode == 'quadratic':
        u = t**2 + a * t + b
        vp = p * t + r
    else:
        u = t**3 + a * t**2 + b * t + 0
        vp = p * t + r
    up = sp.diff(u, t)
    W = sp.expand(u**2 * (up**2 + vp**2) - Dlt * vp**2)
    _, rem = sp.div(W, q, t)
    return [sp.expand(rem.coeff(t, i)) for i in range(n)]


def run(qcoeffs, prime=32003, lex_over='fp'):
    eqs = system(qcoeffs)
    polys = [sp.Poly(e, *vars_, modulus=prime) for e in eqs]
    print("q =", qcoeffs, "  #eqs", len(eqs), flush=True)
    t0 = time.time()
    G = sp.groebner(polys, *vars_, order='grevlex', modulus=prime)
    print("grevlex over F_%d done %.1fs, %d polys" % (prime, time.time() - t0, len(G.polys)), flush=True)
    t0 = time.time()
    Gl = G.fglm('lex')
    print("fglm done %.1fs, %d polys" % (time.time() - t0, len(Gl.polys)), flush=True)
    found = False
    for g in Gl.polys:
        inv = set()
        for m in g.monoms():
            for i, e in enumerate(m):
                if e > 0:
                    inv.add(i)
        if inv <= {4}:
            pd = sp.Poly(g, Dlt, modulus=prime)
            print("Delta-only poly degree", pd.degree())
            print("   ", pd.as_expr())
            found = True
    if not found:
        print("no Delta-only basis element (system possibly positive-dimensional)")


if __name__ == '__main__':
    args = sys.argv[1:]
    qc = [int(v) for v in args[0].split(',')] if args else [1, 0, -5, 0, 4, 1]
    pr = int(args[1]) if len(args) > 1 else 32003
    rr = np.roots(qc)
    print("roots:", np.round(np.sort(rr.real), 4), "max|imag|", float(np.max(np.abs(rr.imag))))
    run(qc, pr)
