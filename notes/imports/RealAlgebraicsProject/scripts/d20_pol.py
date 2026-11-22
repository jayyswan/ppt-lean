"""Session 11: write out the degree-20 polynomials of plane_d20.py (same seeds) for frob_group.py."""
import random, cypari
pari = cypari.pari
def pw(x, k): return sum(v**k for v in x)
def tf(v): m = sum(v) / len(v); return [a - m for a in v]
def Q4(y): return 6*pw(y, 4) - pw(y, 2)**2
def Q5(y): return 18*pw(y, 5) - 5*pw(y, 2)*pw(y, 3)
rnd = random.Random(20); A, B = pari('a'), pari('b')
for trial in range(2):
    while True:
        x = [rnd.randint(-12, 12) for _ in range(9)]
        if len(set(x)) == 9: break
    x = [pari(v) for v in x]
    w = {k: tf([v**k for v in x]) for k in (1, 2, 3)}
    y = [A*u + B*v + z for u, v, z in zip(w[1], w[2], w[3])]
    R = pari.polresultant(Q4(y), Q5(y), B); R = R / pari.content(R)
    fa = pari.factor(R); degs = [int(pari.poldegree(f)) for f in fa[0]]
    print(trial, [int(v) for v in x], degs)
    open('d20_%d.pol' % trial, 'w').write(str(fa[0][degs.index(max(degs))]))
