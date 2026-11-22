# Session 14: monomial-valuation test of the RY lattice condition at a special point of P(Pi).
# For a local monomial order (weight w > 0), each radicand f has leading monomial n_f.
# The A-fixed sheets survive iff for every c in (Z/2)^F with sum c_f n_f in 2Z^7,
# psi(sum c_f n_f / 2) = 1.  (Condition (*) in the log.)
import sys, random, itertools, math, pickle
from newton import setup, support, chars
pt = {'x54': (4,-5), 'x45': (-5,4), 'x8': (1,1), 'gen': (2,-1)}[sys.argv[1]]
group = sys.argv[2]; D = int(sys.argv[3]); N = int(sys.argv[4])
names = ['p2','f4','g6','e4','n8','h6','h7','m12','m13'] + (sys.argv[6].split(',') if len(sys.argv) > 6 else [])
setup(*pt, D, group)
S = {}
for nm in names:
    sp = support(nm, D)
    if (0,)*7 in sp: continue      # unit at the point: no constraint
    S[nm] = list(sp.keys())
print('vanishing at point:', {k: min(map(sum, v)) for k, v in S.items()})
C, mods = chars(group)
def psi(m):
    # m: integer vector over the 7 coordinates -> element of A^* (two components)
    out = []
    for slot in (0, 1):
        g = mods[slot]
        if g == (4,1):
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
        if psi([t//2 for t in tot]) != TRIV:
            return False
    return True
random.seed(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
bad = {}
for it in range(N):
    sc = random.choice([0.5, 1, 2, 3, 5])
    w = [math.exp(random.uniform(-sc, sc)) * (1 + 1e-9*random.random()) for _ in range(7)]
    lead = {}
    for nm, sup in S.items():
        lead[nm] = min(sup, key=lambda n: sum(wi*ni for wi, ni in zip(w, n)))
    if survives(lead):
        key = tuple(sorted(lead.items()))
        bad.setdefault(key, w)
print('surviving leading-monomial patterns:', len(bad))
for k, w in list(bad.items())[:10]:
    print([round(x,3) for x in w]); print('   ', k)
pickle.dump(bad, open('scan_%s_%s.pkl' % (sys.argv[1], group), 'wb'))
