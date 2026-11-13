"""F1 stage B runner: Bring-Jerrard for 20 quintic fields, then the pipeline.

Fields (chosen by F1_bring.choose_fields with coefficient box 3 for S5/A5, and
by a box-5 totally-real search; ordered by polynomial discriminant, which is
the field discriminant times an index square -- PARI is not available to
compute field discriminants):
  10 S5 (all signature (1,2)), 5 A5 (signature (1,2)), 5 totally real S5.

For each field: construct() over several coordinate patterns, keep the
smallest (m, height(h)); then filter_h (primes to 2*10^5), blind certify
(must return a field isomorphic to K) and the Trager check.

Usage:  python3 F1_bring_run.py [construct|pipeline]   (Windows: py -3 ...)
Writes F1_bring_constructions.csv and F1_bring_pipeline.csv (UTF-8, LF).
"""

import csv
import sys
import time

sys.path.insert(0, ".")
from F1_bring import (construct, eliminate, numeric_choice, pick_factor,  # noqa: E402
                      height, fmpz_poly)
from F1_core import (LONG_PRIMES, TableCache, certify, fields_isomorphic,  # noqa: E402
                     filter_h, galois_certificate, has_root_in, N_of,
                     signature, tri)

FIELDS = [
    ("S5", [-1, -2, -2, 1, 2, 1]), ("S5", [-1, -1, -1, 0, 1, 1]),
    ("S5", [-1, -3, -1, 3, 2, 1]), ("S5", [-1, -2, -3, -1, 1, 1]),
    ("S5", [-1, -2, -3, -2, 0, 1]), ("S5", [-1, -3, -3, 0, 1, 1]),
    ("S5", [-1, -1, 0, 0, 0, 1]), ("S5", [-1, -3, -3, -1, 0, 1]),
    ("S5", [-1, -3, -3, -2, -1, 1]), ("S5", [-1, -2, -1, 0, 0, 1]),
    ("A5", [-2, -2, -2, 0, 1, 1]), ("A5", [-1, 1, -1, -2, -1, 1]),
    ("A5", [-2, 3, 2, -2, 0, 1]), ("A5", [-2, -1, -3, -1, 2, 1]),
    ("A5", [-1, -3, -2, 1, -3, 1]),
    ("TR", [-1, 3, 1, -5, 0, 1]), ("TR", [-3, 4, 5, -5, -1, 1]),
    ("TR", [-1, 4, -1, -5, 1, 1]), ("TR", [-3, 5, 4, -5, -1, 1]),
    ("TR", [-1, 3, 2, -5, -1, 1]),
]


def best_construction(f, tries=6):
    best = None
    for choice in range(tries):
        try:
            out = construct(f, box=4, choice=choice)
            P = eliminate(out)
        except Exception:  # a degenerate pattern; try the next one
            continue
        lam, allreal = None, None
        for prec in (256, 1024, 4096):
            try:
                lam, allreal, A, B = numeric_choice(out, prec=prec)
                break
            except ValueError:
                continue
        facs = [g for g, e in P.factor()[1]]
        if lam is not None:
            hs = pick_factor(P, lam)
        elif len(facs) == 1:
            # irreducible eliminant: every conjugate choice gives this h
            hs = [fmpz_poly([int(c) for c in facs[0].numer().coeffs()])]
        else:
            continue
        if len(hs) != 1:
            continue
        h = hs[0]
        if h.degree() < 1:
            continue
        key = (h.degree(), height(h))
        if best is None or key < best[0]:
            best = (key, dict(h=h, point=out["point"], pattern=out["pattern"],
                              tower=[(v, r.degrees()[("a1", "a2", "a3", "a4", "t", "r", "s", "L").index(v)])
                                     for v, r in out["rels"]],
                              allreal=allreal, lam=lam, choice=choice))
    return None if best is None else best[1]


def run_construct():
    rows = []
    for cls, co in FIELDS:
        f = fmpz_poly(co)
        t = time.time()
        b = best_construction(f)
        dt = time.time() - t
        if b is None:
            print(cls, f, "NO CONSTRUCTION")
            rows.append([cls, str(f), "", "", "", "", "", "", "", ""])
            continue
        h = b["h"]
        g = galois_certificate(h) if h.degree() > 1 else ("trivial", "")
        sig = signature(h) if h.degree() > 1 else (1, 0)
        print("%s %-55s m=%d digits(H)=%d tower=%s point=%s real-choice=%s Gal(h)=%s sig(h)=%s %.1fs"
              % (cls, f, h.degree(), len(str(height(h))), b["tower"], b["point"][0], b["allreal"],
                 g[0] if g[1] == "proved" else "unproved(%d patterns)" % len(g[1]), sig, dt))
        rows.append([cls, " ".join(str(c) for c in co), h.degree(), len(str(height(h))),
                     " ".join(str(int(c)) for c in h.coeffs()), b["point"][0],
                     ";".join("%s:%d" % t_ for t_ in b["tower"]), b["allreal"],
                     g[0] if g[1] == "proved" else "unproved", "%d,%d" % sig])
    with open("F1_bring_constructions.csv", "w", encoding="utf-8", newline="\n") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["class", "f_low_to_high", "m", "height_digits", "h_low_to_high", "point",
                    "tower", "real_choice", "gal_h", "sig_h"])
        w.writerows(rows)


def run_pipeline(max_n=None):
    eng = tri(5)
    cache = TableCache(eng)
    out_rows = []
    with open("F1_bring_constructions.csv", encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh))
    for row in rows:
        if not row["m"]:
            continue
        f = fmpz_poly([int(c) for c in row["f_low_to_high"].split()])
        h = [int(c) for c in row["h_low_to_high"].split()]
        m = len(h) - 1
        t = time.time()
        fv = filter_h(h, eng, primes=LONG_PRIMES, need=12, cache=cache)
        t1 = time.time() - t
        t = time.time()
        trag = has_root_in(f, N_of(h, eng))
        t_trag = time.time() - t
        t = time.time()
        if max_n is not None and 5 * m > max_n:
            st, iso, t2 = "skipped", "", 0.0
        else:
            r = certify(h, eng)
            t2 = time.time() - t
            st = r.status
            iso = fields_isomorphic(r.K, f) if r.status == "solution" else ""
        print("%s m=%d filter=%s (%.1fs) certify=%s iso=%s (%.1fs) trager=%s"
              % (row["class"], m, fv, t1, st, iso, t2, trag), flush=True)
        out_rows.append([row["class"], row["f_low_to_high"], m, fv[0], fv[1], st, iso, trag,
                         "%.1f" % t2, "%.1f" % t_trag])
    with open("F1_bring_pipeline.csv", "w", encoding="utf-8", newline="\n") as fh:
        w = csv.writer(fh, lineterminator="\n")
        w.writerow(["class", "f_low_to_high", "m", "filter", "filter_info", "certify",
                    "certified_K_iso_input", "trager_root_in_B_h", "certify_seconds", "trager_seconds"])
        w.writerows(out_rows)


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "construct"
    if mode == "construct":
        run_construct()
    else:
        run_pipeline(int(sys.argv[2]) if len(sys.argv) > 2 else None)
