# Session 15 (run ord6.py 8 first for g8; needs psl_group.py): monomial-valuation test (*) for PSL(2,8)'s V4 (translations by W = {0,1,2,3})
# at the special point x8 = (1,...,1,-8) of P(Pi), with the F''' radicands
# p2, -f4, j6, h6, k6, k6' (and optional extras).
# V4 acts diagonally on both 4-sets, so each nontrivial character has a 2-dim eigenspace
# spanned by e_chi (on W) and e'_chi (on W+4). Local coordinates: s along P(Pi), and for each
# chi two coordinates y in a chosen basis of V_chi (basis given by a 2x2 matrix per chi).
# usage: python3 psl_x8.py <a> <b> <basis: sep|sum|iso|rand> <samples> <seed> [extra radicands]
import sys, itertools, random, math, collections, pickle
import cypari
pari = cypari.pari
pari.allocatemem(10**9)

# ---- PSL(2,8) on P^1(F_8), points 0..7 bit vectors (w^3 = w + 1), 8 = infinity
def fmul(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
def finv(a):
    for b in range(1, 8):
        if fmul(a, b) == 1: return b
INF = 8
def mob(a, b, c, d, z):
    if z == INF: return INF if c == 0 else fmul(a, finv(c))
    num = fmul(a, z) ^ b; den = fmul(c, z) ^ d
    return INF if den == 0 else fmul(num, finv(den))
G = sorted({tuple(mob(a, b, c, d, z) for z in range(9))
            for a, b, c, d in itertools.product(range(8), repeat=4) if fmul(a, d) ^ fmul(b, c)})
assert len(G) == 504
def orbit(mon):  # mon: dict index->exp
    m = tuple(sorted(mon.items()))
    return sorted({tuple(sorted((g[i], e) for i, e in m)) for g in G})

# ---- local coordinates
a, b = int(sys.argv[1]), int(sys.argv[2])
mode = sys.argv[3]; N = int(sys.argv[4]); seed = int(sys.argv[5])
extra = sys.argv[6].split(',') if len(sys.argv) > 6 else []
rnd = random.Random(seed)
W = [0, 1, 2, 3]
def chi(al, v): return (-1) ** bin(al & v).count('1')
if mode == 'sep':  B = {al: [(1, 0), (0, 1)] for al in (1, 2, 3)}
elif mode == 'sum': B = {al: [(1, 1), (1, -1)] for al in (1, 2, 3)}
elif mode == 'iso': B = {al: [(1, 'I'), (1, '-I')] for al in (1, 2, 3)}
else:
    B = {}
    for al in (1, 2, 3):
        while True:
            M = [(rnd.randint(-5, 5), rnd.randint(-5, 5)) for _ in range(2)]
            if M[0][0]*M[1][1] - M[0][1]*M[1][0] != 0 and all(x != 0 for r in M for x in r): break
        B[al] = M
VARS = ['s'] + ['y%d' % k for k in range(1, 7)]
CH = [(0, 0)]   # character of each coordinate as element of (Z/2)^2
coords = [[str(a)] * 1 for _ in range(9)]
base = [a]*4 + [b]*4 + [-4*(a+b)]
pi = [1]*4 + [0]*4 + [-4]
terms = [['(%d)' % base[j], 's*(%d)' % pi[j]] for j in range(9)]
k = 0
for al in (1, 2, 3):
    for (u, v) in B[al]:
        k += 1
        for x in W:
            terms[x].append('y%d*(%s)*(%d)' % (k, u, chi(al, x)))
            terms[4 + x].append('y%d*(%s)*(%d)' % (k, v, chi(al, x)))
        CH.append((al & 1, (al >> 1) & 1))
X = [pari('+'.join(t)) for t in terms]
POW = [[pari(1)] for _ in range(9)]
for j in range(9):
    for e in range(1, 15): POW[j].append(POW[j][-1] * X[j])
def psum(kk): return sum((POW[j][kk] for j in range(9)), pari(0))
def osum(mon):
    tot = pari(0)
    for m in orbit(mon):
        t = pari(1)
        for i, e in m: t = t * POW[i][e]
        tot += t
    return tot
P = {kk: psum(kk) for kk in range(2, 10)}
from fractions import Fraction as Fr
R = {}
R['p2'] = P[2]
R['f4'] = 24*P[4] - 19*P[2]**2
R['g6'] = 231*P[2]**3 - 966*P[2]*P[4] + 1008*P[6] - 256*P[3]**2
R['h6'] = -69*P[2]**3 + 732*P[2]*P[4] + 736*P[3]**2 - 1440*P[6]
R['j6'] = osum({0:1, 1:1, 2:1, 3:1, 4:2})
o24 = osum({0:2, 1:4}); o33 = osum({0:3, 1:3})
q = pari('41/828')*P[6] - pari('43/92')*o24 - pari('13/9')*o33
R['k6'] = osum({0:1, 1:1, 2:2, 3:2}) - q
R['k6p'] = osum({0:1, 1:1, 2:2, 4:2}) - q
R['h7'] = 1440*P[7] - 648*P[2]*P[5] - 980*P[3]*P[4] + 205*P[2]**2*P[3]
R['r9'] = 14*P[2]*R['h7'] + 5*P[3]*R['h6']
_R14 = '255533126625*p2^4*p6 - 3845721038580*p2^3*p3*p5 - 52308485775*p2^3*p4^2 + 1027936734300*p2^3*p8 + 2233063864350*p2^2*p3^2*p4 + 3740357980800*p2^2*p3*p7 - 7384956768000*p2^2*p4*p6 + 9689218887168*p2^2*p5^2 + 4460251150400*p2*p3^4 - 15452363612400*p2*p3^2*p6 + 26247975293520*p2*p3*p4*p5 - 10664283772800*p2*p3*p9 + 2596047892200*p2*p4^3 - 4148470771200*p2*p4*p8 - 31188422321280*p2*p5*p7 + 19025376602400*p2*p6^2 - 8149116117120*p3^3*p5 - 2244196479000*p3^2*p4^2 + 21303834350400*p3^2*p8 + 2451403987200*p3*p4*p7 - 23754104611200*p3*p5*p6 + 5661945752400*p4^2*p6 - 37145405744640*p4*p5^2 + 84575077171200*p5*p9 - 27659611728000*p6*p8 - 11573970508800*p7^2'
R['d6'] = R['k6'] - R['k6p']
R['u6'] = 2592*R['j6'] + 1867*P[2]**3 - 2376*P[2]*P[4]
if 'g8' in extra:
    _o8, _K8, _ = pickle.load(open('ord6_8_6.pkl', 'rb'))
    _c = _K8[int(dict(e.split('=') for e in extra if '=' in e).get('g8col', 17))]
    R['g8'] = pari(0)
    for _j, _cj in enumerate(_c):
        if _cj != '0':
            _t = pari(0)
            for mo in _o8[_j]:
                t1 = pari(1)
                for i, e in mo: t1 = t1 * POW[i][e]
                _t += t1
            R['g8'] += pari(_cj) * _t
if 'R14' in extra:
    R['R14'] = pari(_R14).substvec(pari('[p2,p3,p4,p5,p6,p7,p8,p9]'), [P[i] for i in range(2, 10)])
base_names = ['p2', 'f4', 'j6', 'h6', 'k6', 'k6p']
if 'only' in extra: base_names = []
names = base_names + [e for e in extra if e in R]
pari('mons(F,vs)=if(#vs==0,return([[[],F]]));my(v=vs[1],r=List(),d=poldegree(F,v));for(k=0,d,my(c=polcoef(F,k,v));if(c!=0,my(L=mons(c,vs[2..#vs]));for(j=1,#L,listput(r,[concat([k],L[j][1]),L[j][2]]))));Vec(r)')
vs = pari('[s,y1,y2,y3,y4,y5,y6]')
S, ORD = {}, {}
for nm in names:
    sup = [tuple(int(e) for e in m[0]) for m in pari('mons')(R[nm], vs)]
    o = min(map(sum, sup))
    ORD[nm] = o
    if o == 0: continue
    # keep only minimal elements of the support's Newton polyhedron candidates: monomials not
    # divisible by another support monomial (leading terms for positive weights come from these)
    ss = set(sup)
    mn = [m for m in sup if not any(n != m and all(n[i] <= m[i] for i in range(7)) for n in ss)]
    S[nm] = mn
print('a,b =', (a, b), 'basis', mode, B if mode == 'rand' else '')
print('order of vanishing at point:', ORD)
def psi(m):
    return (sum(mi * CH[x][0] for x, mi in enumerate(m)) % 2, sum(mi * CH[x][1] for x, mi in enumerate(m)) % 2)
def survives(lead):
    F = list(lead.values())
    for c in itertools.product((0, 1), repeat=len(F)):
        if not any(c): continue
        tot = [sum(ci * n[x] for ci, n in zip(c, F)) for x in range(7)]
        if any(t % 2 for t in tot): continue
        if psi([t // 2 for t in tot]) != (0, 0): return False
    return True
bad = {}
for it in range(N):
    sc = rnd.choice([0.5, 1, 2, 3, 5])
    w = [math.exp(rnd.uniform(-sc, sc)) * (1 + 1e-9 * rnd.random()) for _ in range(7)]
    lead = {nm: min(sup, key=lambda n: sum(wi * ni for wi, ni in zip(w, n))) for nm, sup in S.items()}
    if survives(lead):
        bad.setdefault(tuple(sorted(lead.items())), w)
print('surviving leading-monomial patterns:', len(bad))
for kk, w in list(bad.items())[:8]:
    print([round(x, 3) for x in w]); print('   ', kk)
pickle.dump((S, CH, bad), open('pslx8_%d_%d_%s_%d.pkl' % (a, b, mode, seed), 'wb'))
