# scan.py with exact supports (D=14 covers every radicand, max degree 14) and a
# comparison against the degree-12 truncation used in session 14.
import sys, random, itertools, math
from newton import setup, support, chars
pt = {'x54': (4,-5), 'x45': (-5,4), 'x8': (1,1), 'gen': (2,-1)}[sys.argv[1]]
group = sys.argv[2]; N = int(sys.argv[3]); seed = int(sys.argv[4])
names = ['p2','f4','g6','e4','n8','h6','h7','m12','m13'] + sys.argv[5].split(',')
setup(*pt, 14, group)
S = {}; S12 = {}
for nm in names:
    sp_ = support(nm, 14)
    if (0,)*7 in sp_: continue
    S[nm] = list(sp_.keys()); S12[nm] = [m for m in S[nm] if sum(m) <= 12]
C, mods = chars(group)
def psi(m):
    out = []
    for slot in (0, 1):
        if mods[slot] == (4,1):
            out.append(sum(mi * C[x][slot][0] for x, mi in enumerate(m)) % 4)
        else:
            out.append(tuple(sum(mi * C[x][slot][j] for x, mi in enumerate(m)) % 2 for j in (0,1)))
    return out
TRIV = psi([0]*7)
def survives(lead):
    F = list(lead.values())
    for c in itertools.product((0,1), repeat=len(F)):
        if not any(c): continue
        tot = [sum(ci*n[x] for ci, n in zip(c, F)) for x in range(7)]
        if any(t % 2 for t in tot): continue
        if psi([t//2 for t in tot]) != TRIV: return False
    return True
rnd = random.Random(seed)
bad = {}; bad12 = {}; diff = 0
for it in range(N):
    sc = rnd.choice([0.5, 1, 2, 3, 5])
    w = [math.exp(rnd.uniform(-sc, sc)) * (1 + 1e-9*rnd.random()) for _ in range(7)]
    key = lambda n: sum(wi*ni for wi, ni in zip(w, n))
    lead = {nm: min(sup, key=key) for nm, sup in S.items()}
    lead12 = {nm: min(sup, key=key) for nm, sup in S12.items() if sup}
    if lead != lead12: diff += 1
    if survives(lead): bad.setdefault(tuple(sorted(lead.items())), w)
    if survives(lead12): bad12.setdefault(tuple(sorted(lead12.items())), w)
print(sys.argv[1], group, 'samples', N, '| leading monomial changed by truncation:', diff,
      '| surviving exact:', len(bad), '| surviving deg-12:', len(bad12))
for k, w in list(bad.items())[:3]: print('  ', [round(x,3) for x in w], k)
