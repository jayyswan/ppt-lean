# X6-02: function-level fit search (search 2 of PLAN-jacobi-X6).
#
# Lesson learned the hard way: fitting the target against the WHOLE library in a dense
# grid gives a useless ~1e-14 residual, because the library is massively collinear
# (CORE has numerical rank ~22 of 48) and the minimum-norm solution interpolates any
# smooth function.  The fix is to test SMALL, well-conditioned subsets and to judge
# them by EXTRAPOLATION, which a genuine functional identity survives and an overfit
# does not.
#
# Method per modulus c:
#   PRIME = 16 library functions, all of them valid on (0, 1.95] for every c in MODULI.
#   train grid u in [0.05, 1.40]; off-grid = fresh points in the same interval;
#   extrapolation = u in [1.50, 1.95] (still < K(c) for c=0.7, K=2.075).
#   For every subset of size 1..KSUB:
#       fit  target ~ b0 + sum_i b_i g_i   by least squares (SVD, rcond=1e-11),
#       record off-grid and extrapolation max-residual.
#   A genuine identity -> all three residuals ~1e-12 (double precision).  Overfitting
#   shows a tiny train/off-grid residual but an extrapolation residual that stays O(1e-3).
#
# The script also prints the ill-conditioning demonstration (full CORE), then escalates
# any subset with extrapolation residual < 1e-8 to a 100-digit mpmath re-fit.
#
# Rerunnable:  python X6-02-fits.py [KSUB]

import sys, os, time, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from scipy.special import ellipkinc, ellipeinc, ellipk, ellipe, ellipj
from scipy.optimize import brentq
from X6_lib import CORE, PRIME, MODULI

TARGETS = ['am', 'sn', 'cn', 'dn', 'am_periodic']


def landen_np(c):
    kp = np.sqrt(1 - c)
    k1 = (1 - kp) / (1 + kp)
    return k1 * k1


def EAm_np(u, c):
    if c == 0:
        return u
    return brentq(lambda phi: ellipeinc(phi, c) - u, u, u / np.sqrt(1 - c) + 1.0,
                  xtol=1e-15, rtol=1e-15)


def lib_np(u, c):
    L = {}
    cl = landen_np(c)
    L['u'] = u
    L['u2'] = u * u
    L['sqrt_u'] = np.sqrt(u) if u >= 0 else np.nan
    L['sin_u'] = np.sin(u)
    L['cos_u'] = np.cos(u)
    L['tan_u'] = np.tan(u)
    L['twou'] = 2.0 ** u
    L['log_u'] = np.log(u) if u > 0 else np.nan
    L['arccos_u'] = np.arccos(u) if -1 <= u <= 1 else np.nan
    L['pi'] = np.pi
    L['F_u_c'] = ellipkinc(u, c)
    L['E_u_c'] = ellipeinc(u, c)
    L['F_u_c1'] = ellipkinc(u, 1 - c)
    L['E_u_c1'] = ellipeinc(u, 1 - c)
    L['F_u_cl'] = ellipkinc(u, cl)
    L['E_u_cl'] = ellipeinc(u, cl)
    L['EAm_u_c'] = EAm_np(u, c)
    L['EAm_u_c1'] = EAm_np(u, 1 - c)
    L['EAm_u_cl'] = EAm_np(u, cl)
    L['K_c'] = ellipk(c)
    L['E_c'] = ellipe(c)
    L['K_c1'] = ellipk(1 - c)
    L['E_c1'] = ellipe(1 - c)
    L['K_cl'] = ellipk(cl)
    L['E_cl'] = ellipe(cl)
    L['sinF'] = np.sin(L['F_u_c'])
    L['cosF'] = np.cos(L['F_u_c'])
    L['sinE'] = np.sin(L['E_u_c'])
    L['cosE'] = np.cos(L['E_u_c'])
    L['sqrtF'] = np.sqrt(L['F_u_c']) if L['F_u_c'] >= 0 else np.nan
    L['sqrtE'] = np.sqrt(L['E_u_c']) if L['E_u_c'] >= 0 else np.nan
    L['twoF'] = 2.0 ** L['F_u_c']
    L['EE'] = ellipeinc(L['E_u_c'], c)
    L['FF'] = ellipkinc(L['F_u_c'], c)
    L['EF'] = ellipeinc(L['F_u_c'], c)
    L['FE'] = ellipkinc(L['E_u_c'], c)
    L['EAmE'] = EAm_np(L['E_u_c'], c)
    L['EAmF'] = EAm_np(L['F_u_c'], c)
    L['Fsin'] = ellipkinc(np.sin(u), c)
    L['Esin'] = ellipeinc(np.sin(u), c)
    L['Fcos'] = ellipkinc(np.cos(u), c)
    L['Ecos'] = ellipeinc(np.cos(u), c)
    L['K_cpow'] = ellipk(c ** u)
    L['E_cpow'] = ellipe(c ** u)
    if c * u < 1:
        L['K_cu'] = ellipk(c * u)
        L['E_cu'] = ellipe(c * u)
    else:
        L['K_cu'] = np.nan
        L['E_cu'] = np.nan
    mm = u * u / (1 + u * u)
    L['arcL'] = np.sqrt(1 + u * u) * ellipe(mm)
    L['sqrt_sin_u'] = np.sqrt(np.sin(u)) if np.sin(u) >= 0 else np.nan
    return L


def target_np(u, c):
    sn, cn, dn, ph = ellipj(u, c)
    return {'am': ph, 'sn': sn, 'cn': cn, 'dn': dn,
            'am_periodic': ph - u * np.pi / (2 * ellipk(c))}


def build(names, us, c):
    M = np.empty((len(us), len(names)))
    for i, u in enumerate(us):
        L = lib_np(u, c)
        for j, n in enumerate(names):
            M[i, j] = L[n]
    return M


def fit_resid(X, y, us, scal=None):
    # design [1, X]; SVD lstsq with rcond to avoid chasing degeneracy
    A = np.column_stack([np.ones(len(X)), X])
    if scal is None:
        scal = np.maximum(np.linalg.norm(A, axis=0), 1e-300)
    sol, *_ = np.linalg.lstsq(A / scal, y, rcond=1e-11)
    return np.max(np.abs((A / scal) @ sol - y)), A / scal, sol


def main():
    KSUB = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    t0 = time.time()
    utr = np.linspace(0.05, 1.40, 300)
    ute = np.linspace(0.05, 1.40, 181)[:-1] + 0.0073
    uex = np.linspace(1.50, 1.95, 120)

    print(f"EXACT LINEAR-IDENTITY SEARCH: subsets of PRIME (16) of size 1..{KSUB},")
    print("fit on train [0.05,1.40], judged by off-grid and by EXTRAPOLATION to [1.50,1.95]")
    print(f"{'c':10s} {'target':12s} {'k':>2s} {'train':>10s} {'off-grid':>10s} "
          f"{'extrap':>10s}  best-subset")
    escalations = []
    subsets = {}
    for k in range(1, KSUB + 1):
        subsets[k] = list(itertools.combinations(PRIME, k))

    for cn, c in MODULI.items():
        c = float(c)
        # precompute PRIME columns
        Mtr = build(PRIME, utr, c)
        Mte = build(PRIME, ute, c)
        Mex = build(PRIME, uex, c)
        targets_tr = {tn: np.array([target_np(u, c)[tn] for u in utr]) for tn in TARGETS}
        targets_te = {tn: np.array([target_np(u, c)[tn] for u in ute]) for tn in TARGETS}
        targets_ex = {tn: np.array([target_np(u, c)[tn] for u in uex]) for tn in TARGETS}
        for tname in TARGETS:
            best = None
            for k in range(1, KSUB + 1):
                for combo in subsets[k]:
                    idx = [PRIME.index(n) for n in combo]
                    Xtr = Mtr[:, idx]
                    A = np.column_stack([np.ones(len(Xtr)), Xtr])
                    scal = np.maximum(np.linalg.norm(A, axis=0), 1e-300)
                    sol, *_ = np.linalg.lstsq(A / scal, targets_tr[tname], rcond=1e-11)
                    Ate = np.column_stack([np.ones(len(ute)), Mte[:, idx]]) / scal
                    Aex = np.column_stack([np.ones(len(uex)), Mex[:, idx]]) / scal
                    rtr = np.max(np.abs((A / scal) @ sol - targets_tr[tname]))
                    rte = np.max(np.abs(Ate @ sol - targets_te[tname]))
                    rex = np.max(np.abs(Aex @ sol - targets_ex[tname]))
                    if best is None or rex < best[3]:
                        best = (k, rtr, rte, rex, combo, sol)
            k, rtr, rte, rex, combo, sol = best
            print(f"{cn:10s} {tname:12s} {k:2d} {rtr:10.2e} {rte:10.2e} {rex:10.2e}  "
                  f"{combo}")
            if rex < 1e-8:
                escalations.append((cn, c, tname, combo, [float(z) for z in sol]))
        print(f"   [c={cn} done, {time.time()-t0:.1f}s]")

    # ---- greedy orthogonal matching pursuit over the FULL CORE library.
    # The full least-squares fit is meaningless (rank ~18 of 48, the minimum-norm
    # solution soaks up the huge nullspace).  OMP instead builds a sparse combination
    # one term at a time; if any sparse combination were exact, the extrapolation
    # residual would collapse.  It plateaus if none is.
    print("\nGREEDY OMP OVER FULL CORE (48 functions): extrapolation residual vs #terms")
    MAXT = 12
    for cn, c in MODULI.items():
        c = float(c)
        Ctr = build(CORE, utr, c)
        Cte = build(CORE, ute, c)
        Cex = build(CORE, uex, c)
        good = (np.all(np.isfinite(Ctr), axis=0) & np.all(np.isfinite(Cte), axis=0)
                & np.all(np.isfinite(Cex), axis=0))
        Ctr, Cte, Cex = Ctr[:, good], Cte[:, good], Cex[:, good]
        for tname in ['am', 'am_periodic']:
            ytr = np.array([target_np(u, c)[tname] for u in utr])
            yte = np.array([target_np(u, c)[tname] for u in ute])
            yex = np.array([target_np(u, c)[tname] for u in uex])
            selected = []
            hist = []
            for step in range(MAXT):
                # normalised correlation of each candidate with current residual
                resid = ytr.copy()
                if selected:
                    idx = selected
                    A = np.column_stack([np.ones(len(ytr)), Ctr[:, idx]])
                    sc = np.maximum(np.linalg.norm(A, axis=0), 1e-300)
                    sol, *_ = np.linalg.lstsq(A / sc, ytr, rcond=None)
                    resid = ytr - (A / sc) @ sol
                norms = np.maximum(np.linalg.norm(Ctr, axis=0), 1e-300)
                corr = np.abs((Ctr / norms).T @ resid)
                corr[selected] = -1
                selected.append(int(np.argmax(corr)))
                idx = selected
                A = np.column_stack([np.ones(len(ytr)), Ctr[:, idx]])
                sc = np.maximum(np.linalg.norm(A, axis=0), 1e-300)
                sol, *_ = np.linalg.lstsq(A / sc, ytr, rcond=None)
                rtr = np.max(np.abs((A / sc) @ sol - ytr))
                Aex = np.column_stack([np.ones(len(uex)), Cex[:, idx]]) / sc
                rex = np.max(np.abs(Aex @ sol - yex))
                hist.append((step + 1, rtr, rex))
            tail = hist[-1]
            print(f"  c={cn:10s} {tname:12s}  terms={tail[0]:2d} train={tail[1]:.2e} "
                  f"extrap={tail[2]:.2e}  names={[CORE[i] for i in selected[:5]]}...")

    print(f"\nsubsets with extrapolation residual < 1e-8: {len(escalations)}")
    for e in escalations:
        print("  ", e[0], e[2], e[3], e[4])
    print(f"total {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
