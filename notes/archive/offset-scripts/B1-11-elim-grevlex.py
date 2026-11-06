"""B1-11: bounded attempt at the Delta-elimination degree.

greVlex Groebner over F_p for a small-coefficient totally real septic, then (if the
quotient is finite dimensional and not too large) fglm to lex to extract the
polynomial in Delta alone.
"""
import sympy as sp
import time, sys

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)


def system(qcoeffs):
    q = sum(sp.Integer(int(co)) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    u = t**3 + a * t**2 + b * t + c
    up = sp.diff(u, t)
    vp = p * t**2 + qq * t + r
    W = sp.expand(u**2 * (up**2 + vp**2) - Dlt * vp**2)
    _, rem = sp.div(W, q, t)
    return [sp.expand(rem.coeff(t, i)) for i in range(7)]


def main(qcoeffs, prime, max_fglm_dim=3000):
    eqs = system(qcoeffs)
    polys = [sp.Poly(e, *vars_, modulus=prime) for e in eqs]
    print("starting grevlex over F_%d ..." % prime, flush=True)
    t0 = time.time()
    G = sp.groebner(polys, *vars_, order='grevlex', modulus=prime)
    print("grevlex done in %.1fs, %d basis polys" % (time.time() - t0, len(G.polys)), flush=True)
    # standard monomials
    LMs = [g.LM() for g in G.polys]
    std = _standard_monomials(LMs, len(vars_))
    print("quotient dimension (number of complex solutions, if finite):", len(std), flush=True)
    if not std:
        print("positive-dimensional; no finite solution count")
        return
    if len(std) > max_fglm_dim:
        print("quotient too large for fglm (cap %d); reporting dimension only" % max_fglm_dim)
        return
    print("running fglm to lex ...", flush=True)
    t0 = time.time()
    try:
        Gl = G.fglm('lex')
    except Exception as e:
        print("fglm failed:", type(e).__name__, e)
        return
    print("fglm done in %.1fs, %d basis polys" % (time.time() - t0, len(Gl.polys)), flush=True)
    for g in Gl.polys:
        inv = set()
        for m in g.monoms():
            for i, e in enumerate(m):
                if e > 0:
                    inv.add(i)
        if inv <= {6}:
            print("Delta-only poly in lex basis, degree", sp.Poly(g, Dlt, modulus=prime).degree())
            print("   ", sp.Poly(g, Dlt, modulus=prime).as_expr())


def _standard_monomials(LMs, n):
    """Enumerate exponent vectors NOT divisible by any leading monomial, up to a
    generous degree cap.  Returns [] if the monomial ideal looks infinite."""
    LMs = [tuple(m) for m in LMs]
    maxdeg = 0
    for m in LMs:
        maxdeg = max(maxdeg, sum(m))
    # tower of degrees
    result = []
    seen = set()

    def rec(exp, budget):
        e = tuple(exp)
        if e in seen:
            return
        seen.add(e)
        if any(all(e[i] >= LMs[j][i] for i in range(n)) for j in range(len(LMs))):
            return
        result.append(e)
        for i in range(n):
            if sum(e) < budget:
                ne = list(e); ne[i] += 1
                rec(ne, budget)
    # heuristic cap: if more than 2*maxdeg total degree, likely infinite
    rec((0,) * n, 6 * maxdeg + 12)
    # detect runaway
    if len(result) > 200000:
        return []
    return result


if __name__ == '__main__':
    qc = [int(v) for v in sys.argv[1].split(',')] if len(sys.argv) > 1 else [1, 0, -14, 0, 49, 0, -36, 0]
    pr = int(sys.argv[2]) if len(sys.argv) > 2 else 32003
    main(qc, pr)
