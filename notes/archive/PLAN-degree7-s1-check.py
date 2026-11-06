import numpy as np, itertools
def run(factors, const, jreal, seed):
    q = np.poly1d([1.0])
    for fct in factors: q = q * np.poly1d(fct)
    q = q + const
    rts = np.roots(q.coeffs)
    real = [r.real for r in rts if abs(r.imag) < 1e-7]
    z = [r for r in rts if r.imag > 1e-7][0]
    assert len(real) == 5, len(real)
    s = [np.sum(rts**j).real for j in range(7)]
    L = lambda x: np.concatenate([[-np.dot(s[1:7], x)/7], x])
    vals = lambda c: np.array([sum(c[i]*r**i for i in range(7)) for r in rts])
    pk = lambda c, k: np.sum(vals(c)**k).real
    Q = lambda x: pk(L(x), 2); C = lambda x: pk(L(x), 3)
    B = lambda x, y: (Q(x+y) - Q(x-y))/4
    v = lambda P, x: Q(x)*P - 2*B(P, x)*x
    Phi = lambda P, x: C(v(P, x))
    V0 = np.array([[r**i for i in range(7)] for r in rts])
    def mk0(tg): return np.linalg.solve(V0, np.array(tg, dtype=complex)).real
    e = np.round(mk0([1j if abs(r-z) < 1e-7 else -1j if abs(r-np.conj(z)) < 1e-7 else 0 for r in rts])[1:]*1e4)/1e4
    f = np.round(mk0([1 if abs(r-real[0]) < 1e-7 else 0 for r in rts])[1:]*1e4)/1e4
    assert Q(e) < 0 and Q(f) > 0, (Q(e), Q(f))
    a, bb, cc = Q(f), B(e, f), Q(e); t = (-bb + np.sqrt(bb*bb - a*cc))/a; P0 = e + t*f
    V = np.array([[r**i for i in range(7)] for r in rts])
    def mk(w):
        tgt = [1 if abs(r-real[jreal]) < 1e-7 else w if abs(r-z) < 1e-7 else np.conj(w) if abs(r-np.conj(z)) < 1e-7 else 0 for r in rts]
        c = np.linalg.solve(V, np.array(tgt, dtype=complex)); return c.real
    w = -0.5 + np.sqrt(3)/2*1j
    X, sX = mk(w), mk(np.conj(w))
    out = {"Q(P0)": Q(P0), "p123(X)": [pk(X,1), pk(X,2), pk(X,3)], "p123(sX)": [pk(sX,1), pk(sX,2), pk(sX,3)],
           "b1*b2": B(P0, X[1:])*B(P0, sX[1:]), "Phi(X),Phi(sX)": [Phi(P0, X[1:]), Phi(P0, sX[1:])]}
    dp, dm = np.round(X[1:]*1e4)/1e4, np.round(sX[1:]*1e4)/1e4
    g = lambda m: Phi(P0, dp + m*(dm-dp))
    ms = np.linspace(0, 1, 8); fit = np.polyfit(ms, [g(m) for m in ms], 7)
    out["Phi(d+),Phi(d-)"] = [g(0), g(1)]
    out["deg-7 fit leading coeff / scale"] = fit[0]/max(abs(fit))
    grid = np.linspace(0, 1, 2001); gv = [g(m) for m in grid]
    roots = []
    for i in range(2000):
        if gv[i] == 0 or gv[i]*gv[i+1] < 0:
            lo, hi = grid[i], grid[i+1]
            for _ in range(80):
                mid = (lo+hi)/2
                if g(lo)*g(mid) <= 0: hi = mid
                else: lo = mid
            roots.append(lo)
    checks = []
    for m in roots:
        Vs = v(P0, dp + m*(dm-dp)); nrm = np.linalg.norm(Vs); Vs = Vs/nrm; cs = L(Vs)
        ys = vals(cs); scale = np.max(np.abs(ys))
        res = np.poly(ys).real
        checks.append({"m": m, "|v|": nrm, "p1,p2,p3 (rel)": [pk(cs,1)/scale, pk(cs,2)/scale**2, pk(cs,3)/scale**3],
                       "resolvent y6,y5,y4 (rel)": [res[1]/scale, res[2]/scale**2, res[3]/scale**3],
                       "resolvent y3..y0 (rel)": [res[4]/scale**4, res[5]/scale**5, res[6]/scale**6, res[7]/scale**7]})
    out["sign-change roots"] = checks
    return out
import pprint
np.set_printoptions(precision=4)
for args in [([[1,-1],[1,-2],[1,-3],[1,1],[1,2],[1,0,1]], 1/3, 0, 7),
             ([[1,3],[1,-0.5],[1,-2],[1,1],[1,-4],[1,-1,3]], 2/7, 1, 11),
             ([[1,3],[1,-0.5],[1,-2],[1,1],[1,-4],[1,-1,3]], 2/7, 3, 5)]:
    print("=== case", args[1:]); pprint.pprint(run(*args), width=140)
