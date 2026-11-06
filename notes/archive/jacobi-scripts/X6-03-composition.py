# X6-03: composition search (search 3 of PLAN-jacobi-X6).
#
# For each library g in CORE and each elementary h in
#     {sin, cos, arcsin, arccos, sqrt, 2^., log}
# test whether target(u) == h(g(u)) on a train grid, and judge by EXTRAPOLATION.
# Also fit a rational function of degree <= 2 in g:
#     target ~ (a g^2 + b g + c)/(d g + e)
# by linear least squares on  target*(d g + e) - (a g^2+b g+c) = 0, and judge by
# extrapolation.
#
# Rerunnable: python X6-03-composition.py
#
# A genuine composition -> train == off-grid == extrapolation at ~1e-12.

import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import ellipj, ellipk
import importlib.util
_here = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location('fits', os.path.join(_here, 'X6-02-fits.py'))
F = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(F)
from X6_lib import CORE, MODULI

TARGETS = ['am', 'sn', 'cn', 'dn', 'am_periodic']


def hfun(name, x):
    with np.errstate(all='ignore'):
        if name == 'sin':
            return np.sin(x)
        if name == 'cos':
            return np.cos(x)
        if name == 'arcsin':
            return np.arcsin(x) if np.all(np.abs(x) <= 1) else None
        if name == 'arccos':
            return np.arccos(x) if np.all(np.abs(x) <= 1) else None
        if name == 'sqrt':
            return np.sqrt(x) if np.all(x >= 0) else None
        if name == 'two':
            return 2.0 ** x
        if name == 'log':
            return np.log(x) if np.all(x > 0) else None
    return None


def main():
    t0 = time.time()
    utr = np.linspace(0.05, 1.40, 300)
    ute = np.linspace(0.05, 1.40, 181)[:-1] + 0.0073
    uex = np.linspace(1.50, 1.95, 120)
    HS = ['sin', 'cos', 'arcsin', 'arccos', 'sqrt', 'two', 'log']
    hits = []
    print("COMPOSITION SEARCH  target =? h(g(u))  (train [0.05,1.40], extrap [1.5,1.95])")
    print(f"{'c':10s} {'target':12s} best h(g)               train     off-grid   extrap")
    for cn, c in MODULI.items():
        c = float(c)
        Ctr = F.build(CORE, utr, c)
        Cte = F.build(CORE, ute, c)
        Cex = F.build(CORE, uex, c)
        for tname in TARGETS:
            ytr = np.array([F.target_np(u, c)[tname] for u in utr])
            yte = np.array([F.target_np(u, c)[tname] for u in ute])
            yex = np.array([F.target_np(u, c)[tname] for u in uex])
            best = None
            for gi, gname in enumerate(CORE):
                gtr, gte, gex = Ctr[:, gi], Cte[:, gi], Cex[:, gi]
                if not (np.all(np.isfinite(gtr)) and np.all(np.isfinite(gte))
                        and np.all(np.isfinite(gex))):
                    continue
                for h in HS:
                    vtr = hfun(h, gtr)
                    if vtr is None:
                        continue
                    vte = hfun(h, gte)
                    vex = hfun(h, gex)
                    if vte is None or vex is None:
                        continue
                    rtr = np.max(np.abs(vtr - ytr))
                    rte = np.max(np.abs(vte - yte))
                    rex = np.max(np.abs(vex - yex))
                    if best is None or rex < best[3]:
                        best = (f"{h}({gname})", rtr, rte, rex)
                # rational degree<=2 in g: target = (a g^2+b g+c)/(d g+e)
                # total least squares: smallest right singular vector of
                #   [g^2, g, 1, -target*g, -target]
                B = np.column_stack([gtr**2, gtr, np.ones_like(gtr), -ytr*gtr, -ytr])
                sc = np.maximum(np.linalg.norm(B, axis=0), 1e-300)
                _, _, Vt = np.linalg.svd(B / sc, full_matrices=False)
                sol = Vt[-1]
                a, b, cc, d, e = sol
                def rat(g):
                    den = d * g + e
                    with np.errstate(all='ignore'):
                        out = (a * g * g + b * g + cc) / den
                    return out
                rtr = np.max(np.abs(rat(gtr) - ytr))
                rte = np.max(np.abs(rat(gte) - yte))
                rex = np.max(np.abs(rat(gex) - yex))
                if best is None or rex < best[3]:
                    best = (f"rat2({gname})", rtr, rte, rex)
            print(f"{cn:10s} {tname:12s} {best[0]:22s} {best[1]:.2e} {best[2]:.2e} "
                  f"{best[3]:.2e}")
            if best[3] < 1e-8:
                hits.append((cn, tname, best))
        print(f"   [c={cn} done, {time.time()-t0:.1f}s]")
    print(f"\nhits with extrapolation residual < 1e-8: {len(hits)}")
    for h in hits:
        print("  ", h)
    print(f"total {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
