# Session 9: do symmetric lines through s meet Q4 over C(V)(sqrt p2, sqrt -f4, sqrt g6)?
# Specialise at random rational trace-zero x (Hilbert irreducibility): the quartic in t has
# a root in a multiquadratic extension of Q(x) only if its irreducible factors over Q all have
# Galois group an elementary abelian 2-group (degree 1, 2, or V4).
import random, cypari
pari = cypari.pari
def pw(x, j): return sum(t**j for t in x)
def tf(v): m = pari(sum(v)) / len(v); return [t - m for t in v]
def Q4(y): return 6*pw(y, 4) - pw(y, 2)**2
rnd = random.Random(9)
T = pari('t')
summary = {}
for trial in range(60):
    while True:
        x = [rnd.randint(-30, 30) for _ in range(9)]
        if len(set(x)) == 9: break
    x = tf([pari(t) for t in x])
    cov = {k: tf([t**k for t in x]) for k in range(1, 9)}
    for (j, k) in [(1, 2), (1, 3), (1, 4), (2, 3), (1, 5), (2, 4), (3, 4)]:
        y = [a + T*b for a, b in zip(cov[j], cov[k])]
        q = pari.substpol(Q4(y), T, T)
        fa = pari.factor(q)[0]
        groups = []
        for g in fa:
            d = int(pari.poldegree(g))
            groups.append(d if d <= 2 else (d, str(pari.polgalois(g)[3]) if d <= 7 else '?'))
        ok = all((g in (1, 2)) or (isinstance(g, tuple) and g[0] == 4 and g[1] in ('E(4) = 2[x]2',)) for g in groups)
        key = (j, k)
        summary.setdefault(key, {'multiquadratic root possible': 0, 'groups': {}})
        if ok: summary[key]['multiquadratic root possible'] += 1
        gstr = str(groups); summary[key]['groups'][gstr] = summary[key]['groups'].get(gstr, 0) + 1
for key, val in summary.items(): print(key, val)
