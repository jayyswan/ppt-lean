# Sanity checks for P1': (a) real roots of x^p(1-x)^q = lam, gcd(p,q)=1, at most 3;
# (b) genus of the S_d Galois closure of the trinomial / power x power Belyi maps.
import numpy as np
from math import gcd, factorial
from fractions import Fraction
worst = {}
lams = np.concatenate([np.linspace(-50, 50, 401), np.logspace(-6, 3, 200), -np.logspace(-6, 3, 200)])
for p in range(-7, 8):
    for q in range(-7, 8):
        if p == 0 or q == 0 or gcd(abs(p), abs(q)) != 1: continue
        mx = 0
        a = max(0, -p); b = max(0, -q)
        num = np.poly1d([1, 0]) ** (p + a) * np.poly1d([-1, 1]) ** (q + b)
        den = np.poly1d([1, 0]) ** a * np.poly1d([-1, 1]) ** b
        for lam in lams:
            if lam == 0: continue
            r = (num - lam * den).r
            real = [z.real for z in r if abs(z.imag) < 1e-7 and abs(z.real) > 1e-6 and abs(z.real - 1) > 1e-6]
            real = [z for z in real if abs(z**p * (1 - z)**q - lam) < 1e-5 * max(1, abs(lam))]
            mx = max(mx, len(set(np.round(real, 6))))
        worst[(p, q)] = mx
m = max(worst.values())
print("max real roots over gcd=1 pairs, |p|,|q|<=7:", m, "pairs:", len(worst))
print("e.g. pairs reaching it:", [k for k, v in worst.items() if v == m][:6])
# control: p=q=2 (gcd 2) should give 4
num = np.poly1d([1, 0]) ** 2 * np.poly1d([-1, 1]) ** 2
print("control p=q=2, lam=0.01 real roots:", sum(abs(z.imag) < 1e-9 for z in (num - 0.01).r))
def genus(d, ords):
    s = Fraction(-2) + sum(1 - Fraction(1, o) for o in ords)
    return 1 + Fraction(factorial(d)) * s / 2
print("trinomial D=9 (orders 9, 8, 2):", genus(9, [9, 8, 2]))
print("pp (5,4) (orders 20, 9, 2):", genus(9, [20, 9, 2]))
