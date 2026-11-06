# X6-01: fixed-u integer-relation (PSLQ) search for the X6 identity hunt.
#
# Search space (exact):
#   for each modulus c in MODULI and each u in U_PRIMARY (the 3 brief values),
#   (a) one PSLQ on the FULL core vector [target, CORE..., 1] for target 'am';
#   (b) PSLQ on every subset of PRIME of size 1..SUBSET_MAX, vector
#       [target, subset..., 1].
#   (u in U_RETEST is used only to re-test hits, per the brief.)
#   A hit = integer relation with target coefficient != 0 and residual < 1e-80.
#   Every hit is re-tested at the 5 values U_RETEST (same c); it "holds" only if the
#   residual there is also < 1e-50.
#
# Rerunnable:  python X6-01-pslq.py [subset_max]
#   subset_max default 2 (size<=2 subsets).  Use 3 for the deeper (slower) sweep.

import sys, os, time, itertools, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp
from X6_lib import (CORE, PRIME, PRIME3, MODULI, U_PRIMARY, U_RETEST,
                    library, targets, DPS)

mp.mp.dps = DPS
TARGETS = ['am', 'sn', 'cn', 'dn', 'am_periodic']
RESID_FOUND = mp.mpf(10) ** (-80)
RESID_HOLDS = mp.mpf(10) ** (-50)


def pslq_subset(tgt, subset_vals, maxcoeff):
    vals = [tgt] + subset_vals + [mp.mpf(1)]
    if any(v is None for v in vals):
        return None
    try:
        r = mp.pslq(vals, tol=mp.mpf(10) ** (-85), maxcoeff=maxcoeff, maxsteps=10000)
    except Exception:
        return None
    if r is None:
        return None
    if r[0] == 0:
        return None
    # sanity: residual
    res = abs(sum(a * b for a, b in zip(r, vals)))
    if res > RESID_FOUND:
        return None
    return r


def residual_at(u, c, tname, names, coeffs):
    L = library(u, c)
    T = targets(u, c)
    vals = [T[tname]] + [L[n] for n in names] + [mp.mpf(1)]
    if any(v is None for v in vals):
        return None
    return abs(sum(a * b for a, b in zip(coeffs, vals)))


def main():
    subset_max = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    only_c = sys.argv[2] if len(sys.argv) > 2 else None
    cnames = [only_c] if only_c else list(MODULI.keys())
    found = []
    t0 = time.time()
    n_calls = 0

    for cn in cnames:
        c = MODULI[cn]
        for ui, u in enumerate(U_PRIMARY):
            if time.time() - t0 > 55:
                print(f"[time guard] stopping primary sweep at c={cn}, u-index {ui}")
                break
            L = library(u, c)
            T = targets(u, c)
            for tname in TARGETS:
                tgt = T[tname]
                # (a) full core, only for the principal target 'am'
                if tname == 'am':
                    sub = [L[n] for n in CORE]
                    r = pslq_subset(tgt, sub, 10 ** 10)
                    n_calls += 1
                    if r is not None:
                        found.append(dict(c=cn, u=mp.nstr(u, 12), target=tname, kind='core',
                                          names=CORE, coeffs=[int(z) for z in r], resid=mp.nstr(abs(sum(a*b for a,b in zip(r,[tgt]+sub+[mp.mpf(1)]))), 5)))
                # (b) subsets of PRIME (size <=2) and PRIME3 (size 3)
                for k in range(1, subset_max + 1):
                    basis = PRIME if k <= 2 else PRIME3
                    for combo in itertools.combinations(basis, k):
                        sub = [L[n] for n in combo]
                        r = pslq_subset(tgt, sub, 10 ** 12)
                        n_calls += 1
                        if r is not None:
                            names = list(combo)
                            found.append(dict(c=cn, u=mp.nstr(u, 12), target=tname,
                                              kind=f'sub{k}',
                                              names=names,
                                              coeffs=[int(z) for z in r],
                                              resid=mp.nstr(abs(sum(a*b for a,b in zip(r,[tgt]+sub+[mp.mpf(1)]))), 5)))
            print(f"  c={cn:10s} u={mp.nstr(u,6):>6s}  cumulative hits={len(found)}  calls={n_calls}  t={time.time()-t0:.1f}s")

    print()
    print(f"PSLQ subset search: subset_max={subset_max}, {n_calls} calls, {time.time()-t0:.1f}s")
    print(f"raw hits: {len(found)}")
    for h in found:
        print(f"  [{h['kind']}] c={h['c']} u={h['u']} target={h['target']} resid={h['resid']}")
        print(f"      coeffs={h['coeffs']}")
        print(f"      names={h['names']}")

    # re-test every hit at the 5 re-test u (same c)
    print()
    print("re-test of raw hits at 5 other u:")
    for h in found:
        c = MODULI[h['c']]
        resids = []
        for u in U_RETEST:
            rr = residual_at(u, c, h['target'], h['names'], h['coeffs'])
            resids.append(rr)
        ok = all(rr is not None and rr < RESID_HOLDS for rr in resids)
        h['retest'] = [mp.nstr(rr, 5) if rr is not None else 'NA' for rr in resids]
        h['holds'] = ok
        print(f"  c={h['c']} target={h['target']} names={h['names']} holds={ok} "
              f"retest={h['retest']}")

    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'X6-pslq-results.json')
    prior = []
    if os.path.exists(out):
        try:
            with open(out) as f:
                prior = json.load(f)
        except Exception:
            prior = []
    # de-duplicate on (c,target,names,coeffs)
    seen = {(h.get('c'), h.get('target'), tuple(h.get('names', [])), tuple(h.get('coeffs', [])))
            for h in prior}
    for h in found:
        key = (h['c'], h['target'], tuple(h['names']), tuple(h['coeffs']))
        if key not in seen:
            prior.append(h)
            seen.add(key)
    with open(out, 'w') as f:
        json.dump(prior, f, indent=1)
    print(f"\nwrote {out} ({len(prior)} accumulated raw hits)")


if __name__ == '__main__':
    main()
