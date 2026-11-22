# mult69.py  (session 69)
# Multiplicity of V = {Tr y = Tr y^3 = Tr y^5 = 0} (in P^9, split coordinates) at an
# F-rational point Pt, and the residual of a generic plane through Pt.
# usage: python3 mult69.py <pattern> <trials> <seed>
#   pattern: comma list of 10 values for Pt, e.g. 1,1,1,-1,-1,-1,0,0,0,0
# For each trial: random integer trace-zero u, w; plane y = z*Pt + s*u + t*w;
# R(z,s) = Res_t(Tr y^3, Tr y^5) (degree 15); prints the order of R at s = 0,
# then the residual points: count, distinct coordinates (generator), smoothness
# (rank of [1, y^2, y^4] = 3), max residual.
import sys, random
import sympy as sp
import numpy as np

pat = [sp.Rational(x) for x in sys.argv[1].split(',')]
trials = int(sys.argv[2]); seed = int(sys.argv[3])
random.seed(seed)
z, s, t = sp.symbols('z s t')
assert sum(pat) == 0 and sum(x**3 for x in pat) == 0 and sum(x**5 for x in pat) == 0

def rtz():
    v = [random.randint(-9, 9) for _ in range(9)]
    return v + [-sum(v)]

for tr in range(trials):
    u, w = rtz(), rtz()
    y = [z*pat[i] + s*u[i] + t*w[i] for i in range(10)]
    F3 = sp.expand(sum(yi**3 for yi in y))
    F5 = sp.expand(sum(yi**5 for yi in y))
    R = sp.Poly(sp.resultant(F3, F5, t), z, s)
    Rz = sp.Poly(R.as_expr().subs(z, 1), s)
    coeffs = Rz.all_coeffs()[::-1]
    order = next(i for i, c in enumerate(coeffs) if c != 0)
    deg = Rz.degree()
    # residual points in the chart z = 1 (points at infinity reported separately)
    resid = sp.Poly(sp.quo(Rz.as_expr(), s**order), s)
    sqf = sp.degree(sp.gcd(resid, resid.diff(s)), s) == 0
    roots = np.roots([complex(c) for c in resid.all_coeffs()])
    ok_gen = ok_smooth = 0; maxres = 0.0; npts = 0
    f3 = sp.lambdify((s, t), F3.subs(z, 1)); f5 = sp.lambdify((s, t), F5.subs(z, 1))
    for r in roots:
        # common t-root: roots of F3(r, t) checked against F5
        p3 = sp.Poly(F3.subs({z: 1}), t)
        cs = [complex(sp.N(c.subs(s, r))) for c in p3.all_coeffs()] if False else None
        c3 = [complex(sp.lambdify(s, c)(r)) for c in p3.all_coeffs()]
        tc = np.roots(c3)
        best = min(tc, key=lambda tt: abs(f5(r, tt)))
        yv = np.array([float(pat[i]) + r*u[i] + best*w[i] for i in range(10)])
        res = max(abs(yv.sum()), abs((yv**3).sum()), abs((yv**5).sum())) / max(1, np.abs(yv).max()**5)
        maxres = max(maxres, res); npts += 1
        d = min(abs(yv[i]-yv[j]) for i in range(10) for j in range(i+1, 10))
        ok_gen += d > 1e-6
        M = np.array([np.ones(10), yv**2, yv**4])
        sv = np.linalg.svd(M, compute_uv=False)
        ok_smooth += sv[-1]/sv[0] > 1e-9
    print(f"trial {tr}: deg R(1,s) = {deg}, order at s=0: {order}, residual roots: {npts}, "
          f"squarefree: {sqf}, generators: {ok_gen}, smooth: {ok_smooth}, max rel residual {maxres:.1e}",
          flush=True)
