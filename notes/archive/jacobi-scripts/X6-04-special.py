# X6-04: special arguments u = mK/n (search 4 of PLAN-jacobi-X6).
#
# At u = m K(c)/n the value x = sn(u,c) is algebraic.  If x is a root of a polynomial of
# degree <= 6 whose coefficients are P-constructible, then sn(u,c) is P-constructible and
# hence am(u,c) = arcsin(sn(u,c)) is P-constructible (arcsin/arccos is a known black box).
#
# We look for the minimum degree over (i) the rationals Q and (ii) the natural
# P-constructible field Q(sqrt(1-c)), i.e. coefficients in Z[sqrt(1-c)].
#
# IMPORTANT (spurious-relation control): a PSLQ relation among k numbers at precision D is
# only trustworthy when the coefficient bound M satisfies  M << 10^(D/k); otherwise a
# "relation" of size ~10^(D/k) is expected by chance (this bit us at D=100).  We therefore
# run PSLQ at D = 160 digits with maxcoeff = 10^8 (k <= 14 -> chance floor ~10^11), and
# RE-VERIFY every relation at D = 350 digits, requiring residual < 10^-280.  A 160-digit
# coincidence survives to ~10^-160 only and is rejected.
#
# Method: incremental PSLQ on [1,x,...,x^d] (basis Q) and on
# [1,x,...,x^d, s, s x, ..., s x^d] with s = sqrt(1-c) (basis Z[s]).
#
# Rerunnable:  python X6-04-special.py [DMAX]

import sys, os, time, math, importlib.util
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath as mp

DPS_PSLQ = 160
DPS_VERIFY = 350
MAXCOEFF = 10 ** 8
TOL = mp.mpf(10) ** (-(DPS_PSLQ - 15))
VERIFY_TOL = mp.mpf(10) ** (-280)


def sn_at(m, n, cpair):
    """sn(mK/n) with the modulus reconstructed at the current precision.

    cpair is an exact rational (num, den); this matters because the 350-digit
    re-verification is meaningless if c itself only carries 160 digits (1/2 is
    exact in binary, so this bug is invisible at c=1/2 but corrupts 1/3, 7/10).
    """
    c = mp.mpf(cpair[0]) / cpair[1]
    Kc = mp.ellipk(c)
    return mp.ellipfun('sn', m * Kc / n, c), c


def _rc(r, k):
    return r[k] if 0 <= k < len(r) else 0


def poly_resid(x, r, d, gens):
    val = mp.mpf(0)
    for gi, gg in enumerate([mp.mpf(1)] + gens):
        for i in range(d + 1):
            val += _rc(r, gi * (d + 1) + i) * gg * x ** i
    return abs(val)


def reduce_gcd(r):
    g = 0
    for z in r:
        g = math.gcd(g, abs(int(z)))
    if g > 1:
        r = [int(z) // g for z in r]
    return r


def find_degree(m, n, cpair, gens, dmax):
    """Minimum d with a *verified* relation on [(g x^i)], g in {1}+gens, i<=d."""
    mp.mp.dps = DPS_PSLQ
    x, c = sn_at(m, n, cpair)
    s = mp.sqrt(1 - c) if gens else None
    gvals = [mp.mpf(1)] + ([s] if gens else [])
    for d in range(1, dmax + 1):
        vals = []
        for gg in gvals:
            for i in range(d + 1):
                vals.append(gg * x ** i)
        try:
            r = mp.pslq(vals, tol=TOL, maxcoeff=MAXCOEFF, maxsteps=200000)
        except Exception:
            r = None
        if r is None:
            continue
        while len(r) > 1 and r[-1] == 0:
            r = r[:-1]
        if all(z == 0 for z in r):
            continue
        r = reduce_gcd(r)
        ng = len(gvals)
        deg = max(i for i in range(d + 1)
                  if any(_rc(r, gi * (d + 1) + i) != 0 for gi in range(ng)))
        if deg <= 0:
            continue
        # ---- independent re-verification at DPS_VERIFY (rebuild c exactly) ----
        mp.mp.dps = DPS_VERIFY
        xh, cch = sn_at(m, n, cpair)
        sh = mp.sqrt(1 - cch) if gens else None
        gs = [sh] if gens else []          # poly_resid prepends the constant itself
        res = poly_resid(xh, r, d, gs)
        mp.mp.dps = DPS_PSLQ
        if res < VERIFY_TOL:
            return deg, r, res
        # else: 250-digit coincidence; keep increasing d
    return None, None, None


def poly_str(r, d, gens, var='x'):
    ng = 1 + len(gens)
    terms = []
    for i in range(d + 1):
        ai = _rc(r, i)
        bi = _rc(r, (d + 1) + i) if gens else 0
        if ai == 0 and bi == 0:
            continue
        if not gens or bi == 0:
            coef = f"{ai}"
        elif ai == 0:
            coef = f"{bi}*s"
        else:
            coef = f"({ai}+{bi}*s)"
        terms.append(f"{coef}*{var}^{i}" if i else coef)
    return " + ".join(terms)


def main():
    DMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    t0 = time.time()
    cases = []
    for n in [2, 3, 4, 5, 6, 7, 8]:
        ms = range(1, n) if n <= 5 else ([1, n - 1] if n == 6 else [1, 2])
        for m in ms:
            cases.append((n, m))
    print(f"PSLQ dps={DPS_PSLQ}, maxcoeff=10^8, verify dps={DPS_VERIFY} (resid<10^-280); "
          f"DMAX={DMAX}")
    for cn, cpair in [('1/2', (1, 2)), ('1/3', (1, 3)), ('7/10', (7, 10))]:
        mp.mp.dps = DPS_PSLQ
        cc = mp.mpf(cpair[0]) / cpair[1]
        Kc = mp.ellipk(cc)
        s = mp.sqrt(1 - cc)
        print(f"\n==== c = {cn}   K(c) = {mp.nstr(Kc, 20)}   s = {mp.nstr(s, 20)}")
        print(f"{'n':>2s} {'m':>2s} {'sn(u)':>20s} {'degQ':>5s} {'degZ[s]':>7s} "
              f"{'<=6?':>4s}   primitive poly")
        for (n, m) in cases:
            dq, rq, resq = find_degree(m, n, cpair, [], DMAX)
            ds, rs, ress = find_degree(m, n, cpair, [1], DMAX)
            mp.mp.dps = DPS_PSLQ
            x, _ = sn_at(m, n, cpair)
            ok = (ds is not None and ds <= 6) or (dq is not None and dq <= 6)
            ps = poly_str(rs, ds, [1]) if ds is not None else (
                poly_str(rq, dq, []) if dq is not None else 'NONE <= DMAX')
            print(f"{n:2d} {m:2d} {mp.nstr(x,20):>20s} "
                  f"{(str(dq) if dq else '>'+str(DMAX)):>5s} "
                  f"{(str(ds) if ds else '>'+str(DMAX)):>7s} "
                  f"{('YES' if ok else 'no'):>4s}   {ps}")
        print(f"   [c={cn} done, {time.time()-t0:.1f}s]")
    print(f"\ntotal {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
