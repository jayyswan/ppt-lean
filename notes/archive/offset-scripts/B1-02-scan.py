"""B1-02: real-feasibility scan of the decic line covering system.

For many random TOTALLY REAL septics q (rational coefficients), solve
  W := u^2 (u'^2 + v'^2) - Delta v'^2  divisible by q
for u monic cubic, v' quadratic, Delta real.  Equivalent to 7 equations in
(a,b,c,p,q,r,Delta) = W mod q = 0.

We count distinct real solutions (modulo v' -> -v'), report Delta>0 fraction,
and the sign of the crossing at each root.
"""
import numpy as np
import sympy as sp
import time, json, sys
from scipy.optimize import root

t, a, b, c, p, qq, r, Dlt = sp.symbols('t a b c p qq r Delta')
vars_ = (a, b, c, p, qq, r, Dlt)


def make_system(qcoeffs):
    q = sum(sp.Integer(int(round(co))) * t ** (7 - i) for i, co in enumerate(qcoeffs))
    u = t ** 3 + a * t ** 2 + b * t + c
    up = sp.diff(u, t)
    vp = p * t ** 2 + qq * t + r
    W = sp.expand(u ** 2 * (up ** 2 + vp ** 2) - Dlt * vp ** 2)
    _, rem = sp.div(W, q, t)
    eqs = [sp.expand(rem.coeff(t, i)) for i in range(7)]
    return q, eqs


def solve_one(eqs_f, n_starts=300, seed=0, tol=1e-7):
    rng = np.random.default_rng(seed)
    sols = []
    for s in range(n_starts):
        x0 = rng.normal(size=7) * np.array([2., 4., 4., 2., 4., 4., 4.])
        try:
            res = root(lambda x: np.asarray(eqs_f(*x), float), x0,
                       method='hybr', options={'maxfev': 3000})
        except Exception:
            continue
        if not res.success:
            continue
        val = np.max(np.abs(np.asarray(eqs_f(*res.x), float)))
        if val < tol:
            sols.append(res.x.copy())
    # dedupe including v' sign
    cand = []
    for x in sols:
        xs = x.copy(); xs[3:6] *= -1.0
        if not any(np.max(np.abs(x - y)) < 1e-5 for y in cand):
            cand.append(x)
    return cand


def is_totally_real(qc, tol=1e-8):
    rr = np.roots(qc)
    return np.max(np.abs(rr.imag)) < tol, rr


def main():
    q0 = np.array([1., 0, -7, 0, 14, 0, -7, 0])
    rng = np.random.default_rng(2026)
    n_tot = 0
    stats = []
    t0 = time.time()
    for trial in range(40):
        # random rational perturbation of the Chebyshev septic, small enough to stay totally real
        pert = rng.integers(-40, 41, size=7) / 100.0   # coefficients of t^1..t^6? use all
        qc = q0.copy()
        qc[0] = 1.0
        for k in range(7):
            qc[k] += pert[k]
        good, rr = is_totally_real(qc)
        if not good:
            continue
        n_tot += 1
        # rationalize to integers for exact system (multiply to clear denominators)
        denom = 100
        qci = [int(round(v * denom)) for v in qc]
        g = 0
        for v in qci:
            g = np.gcd(g, abs(v))
        qci = [v // g for v in qci]
        qc_float = [v / qci[0] for v in qci]
        good2, rr2 = is_totally_real(qc_float)
        if not good2:
            continue
        qsym, eqs = make_system(qci)
        f = sp.lambdify(vars_, eqs, 'numpy')
        sols = solve_one(f, n_starts=250, seed=trial)
        realsols = [x for x in sols if np.all(np.isfinite(x)) and x[6] > -1e-6]
        posd = [x for x in realsols if x[6] > 1e-6]
        stats.append({
            'trial': trial, 'q': qci,
            'n_solutions': len(sols), 'n_delta_nonneg': len(realsols),
            'n_delta_pos': len(posd),
            'max_resid': float(max((np.max(np.abs(np.asarray(f(*x), float))) for x in sols), default=-1)),
            'delta_range': [float(min((x[6] for x in posd), default=0)),
                            float(max((x[6] for x in posd), default=0))],
        })
        print("trial %2d  q=%s  n=%d  Delta>0:%d  Delta range %s  [%.1fs]"
              % (trial, qci, len(sols), len(posd),
                 stats[-1]['delta_range'], time.time() - t0), flush=True)
        if n_tot >= 20:
            break
    print("\n=== summary ===")
    print("totally real septics tested:", len(stats))
    print("all had a real solution:", all(s['n_solutions'] > 0 for s in stats))
    print("all had Delta>0 solution:", all(s['n_delta_pos'] > 0 for s in stats))
    print("n_solutions (mod v' sign):", [s['n_solutions'] for s in stats])
    json.dump(stats, open(r"C:\dev\Powerpoint\lean\archived files\offset-scripts\B1-02-stats.json", 'w'), indent=1)


if __name__ == '__main__':
    main()
