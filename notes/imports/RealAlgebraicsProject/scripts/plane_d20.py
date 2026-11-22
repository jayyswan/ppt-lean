"""Session 10: Galois group of the 20 points of D = {Q4 = Q5 = 0} on the symmetric plane
span(s', (s^2)', (s^3)'), specialised at random rational x (Frobenius cycle types),
and how often the quartic line step Q4(s' + t (s^2)') = 0 has a real root for real s.
Run: python3 plane_d20.py
"""
import random, collections, cypari, numpy as np
pari = cypari.pari
def pw(x, k): return sum(v**k for v in x)
def tf(v): m = sum(v) / len(v); return [a - m for a in v]
def Q4(y): return 6*pw(y, 4) - pw(y, 2)**2
def Q5(y): return 18*pw(y, 5) - 5*pw(y, 2)*pw(y, 3)

rnd = random.Random(20)
A, B = pari('a'), pari('b')
for trial in range(2):
    while True:
        x = [rnd.randint(-12, 12) for _ in range(9)]
        if len(set(x)) == 9: break
    x = [pari(v) for v in x]
    w = {k: tf([v**k for v in x]) for k in (1, 2, 3)}
    y = [A*u + B*v + z for u, v, z in zip(w[1], w[2], w[3])]
    R = pari.polresultant(Q4(y), Q5(y), B)
    R = R / pari.content(R)
    fa = pari.factor(R)
    degs = [int(pari.poldegree(f)) for f in fa[0]]
    print('trial', trial, 'x =', [int(v) for v in x], ' factor degrees', degs)
    f = fa[0][degs.index(max(degs))]
    disc = pari.poldisc(f)
    ct = collections.Counter()
    for p in pari.primes(1500):
        if int(p) < 50 or disc % p == 0 or pari.pollead(f) % p == 0: continue
        fp = pari.factormod(f, p)[0]
        ct[tuple(sorted(int(pari.poldegree(pari.lift(g))) for g in fp))] += 1
    tot = sum(ct.values())
    n20 = sum(v for k, v in ct.items() if k == (20,))
    n1 = sum(v for k, v in ct.items() if 1 in k)
    print('   primes', tot, ' 20-cycles %.3f (S20: 0.050)' % (n20 / tot),
          ' with a fixed point %.3f (S20: 0.632)' % (n1 / tot),
          ' distinct cycle types', len(ct))

# real-root frequency of the quartic step for real s, r = 9 (random real vectors)
rng = np.random.default_rng(1)
hits = 0; N = 20000
for _ in range(N):
    s = rng.normal(size=9); s -= s.mean()
    w = s**2; w -= w.mean()
    # Q4(s + t w) as a polynomial in t
    ts = np.linspace(-3, 3, 7)
    vals = [6*np.sum((s + t*w)**4) - np.sum((s + t*w)**2)**2 for t in ts]
    c = np.polyfit(ts, vals, 4)
    r = np.roots(c)
    hits += np.any(np.abs(r.imag) < 1e-9)
print('quartic step has a real root for %.3f of random real s' % (hits / N))
