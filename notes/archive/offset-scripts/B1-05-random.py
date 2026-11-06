"""B1-05: generate random totally real septics not tied to Chebyshev, and report
the PSLQ degree of the covering auxiliary unknowns (tight tolerance)."""
import numpy as np
import sympy as sp
import subprocess, sys, os

PY = r"C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe"
B1_04 = r"C:\dev\Powerpoint\lean\archived files\offset-scripts\B1-04-generic-auxdegree.py"

rng = np.random.default_rng(4242)
found = []

# strategy: perturb Chebyshev q0 by random integers of moderate size; accept totally real
q0 = np.array([1., 0, -7, 0, 14, 0, -7, 0])
for trial in range(20000):
    c = q0.copy()
    for k in range(1, 8):
        c[k] += rng.integers(-8, 9)
    # also random shift to break symmetry
    sh = rng.integers(-3, 4)
    # substitute t -> t + sh : recompute coefficients
    p = np.poly1d(c)
    c2 = p(np.poly1d([1, sh])).c  # coefficients of p(t+sh), high->low
    rr = np.roots(c2)
    if np.max(np.abs(rr.imag)) < 1e-6:
        ci = [int(round(v)) for v in c2]
        g = 0
        for v in ci:
            g = np.gcd(g, abs(v))
        ci = [v // g for v in ci]
        # reject if |coeffs| too large or discriminant 0
        if max(abs(v) for v in ci) > 400:
            continue
        found.append(ci)
    if len(found) >= 4:
        break

print("found septics:")
for f in found:
    print(f)

for f in found[:2]:
    print("\n===== running aux-degree for", f, "=====", flush=True)
    subprocess.run([PY, B1_04, str(f)])

