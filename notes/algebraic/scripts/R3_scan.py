"""Scan tau classes for nondegenerate points of V_tau.

Affine maps tau -> u*tau+v (u != 0) preserve W_tau = span{1,tau,tau^2}, hence V_tau.
So for a field with no proper subfields (S_n Galois group) the classes are:
    tau = beta + u beta^2 + v beta^3,   tau = beta^2 + w beta^3,   tau = beta^3.
We scan integer representatives [0,D,U,V] and [0,0,D,V] (common scaling is harmless).

Usage: py -3 R3_scan.py n6 H Umax Vmax
"""

import sys
from fractions import Fraction

from R3_experiments import classify
from R3_search import NF, Q5, Q6, Q7

QS = {"n5": Q5, "n6": Q6, "n7": Q7}


def main():
    mode, H, umax, vmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    F = NF([int(x) for x in QS[mode]])
    n = F.n
    hits = []
    taus = []
    for D in range(1, 5):
        for U in range(-umax, umax + 1):
            for V in range(-vmax, vmax + 1):
                taus.append([0, D, U, V] + [0] * (n - 4))
    # tau = beta^2 + w beta^3 (no linear term)
    for U in range(1, 5):
        for V in range(-vmax, vmax + 1):
            taus.append([0, 0, U, V] + [0] * (n - 4))
    for tau in taus:
        recs = classify(F, tau, H)
        extra = [r for r in recs if r[3] in ("pd", "nd", "ind")]
        if extra:
            hits.append((tau, extra))
            desc = ", ".join(
                f"{r[3]}:{tuple(str(x) for x in r[1])}" for r in extra[:3]
            )
            print(f"tau={tau[:4]}  nondeg={len(extra)}  {desc}", flush=True)
    print(f"scanned {len(taus)} tau; {len(hits)} with nondegenerate points")


if __name__ == "__main__":
    main()
