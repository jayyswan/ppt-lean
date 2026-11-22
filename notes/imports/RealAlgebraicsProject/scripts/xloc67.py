# S67.2: certified smooth Q_p-points of X_A = {Tr y = Tr y^3 = 0} for an etale algebra
# A = prod Q[x]/(g_j) (any g_j), by line sections: an integer line in {Tr = 0} on which the
# restricted cubic is squarefree over Q and has a Q_p-root (polrootspadic) => smooth Q_p-point.
# Usage: python3 xloc67.py "<g1>;<g2>;..." <p> <lines> <seed> [B]
import sys, random, cypari
pari = cypari.pari
gs = [pari(s) for s in sys.argv[1].split(';')]; p = int(sys.argv[2]); L = int(sys.argv[3])
random.seed(int(sys.argv[4])); B = int(sys.argv[5]) if len(sys.argv) > 5 else 5
dims = [int(pari.poldegree(g)) for g in gs]
def elt(v):
    out=[]; i=0
    for g,d in zip(gs,dims):
        out.append(pari.Mod(pari.Pol(list(reversed(v[i:i+d])) or [0]), g)); i+=d
    return out
def tr(e): return sum(pari.trace(c) for c in e)
def pw(e,k): return [c**k for c in e]
n = sum(dims); hits = 0
for it in range(L):
    while True:
        P = [random.randint(-B,B) for _ in range(n)]; Q = [random.randint(-B,B) for _ in range(n)]
        eP, eQ = elt(P), elt(Q)
        # move into Tr = 0 by subtracting multiples of 1 in the first factor... use y - (Tr y / n) * 1
        tP, tQ = tr(eP), tr(eQ)
        eP = [c - tP/n for c in eP]; eQ = [c - tQ/n for c in eQ]
        break
    t = pari('t')
    y = [a + t*b for a,b in zip(eP,eQ)]
    F = pari.simplify(sum(pari.trace(c**3) for c in y))
    if pari.poldegree(F,t) < 3 or not pari.issquarefree(F): continue
    F = F * pari.denominator(pari.content(F))
    try:
        r = pari.polrootspadic(F, p, 20)
    except Exception as ex:
        continue
    if len(r) > 0:
        hits += 1
        if hits == 1: print('certificate: line P =', P, 'Q =', Q, ' cubic', F, ' Q_p-roots:', len(r))
print('A =', sys.argv[1], ' p =', p, ' lines with a simple Q_p-root:', hits, 'of', L)
