# prod66.py -- certified p-adic plane sections for a product algebra A = prod Q_p[x]/(g_j) given by its factors,
# with planes in coordinates adapted to the factors (pi_j-power bases) and valuation-weighted random entries.
# usage: python3 prod66.py "<g1>;<g2>;..." <p> <planes> <seed> <B> <wmax>
# A plane: y = Y0 + s Y1 + t Y2 inside {Tr y = 0}; entry for coordinate (j,i) = p^w * randint(-B,B), w random in [0,wmax]
# per plane and coordinate. Prints the number of planes with a smooth Q_p-point (degree-15 squarefree resultant).
import sys, random, cypari
pari = cypari.pari; pari.allocatemem(10**9)
G = [pari(g) for g in sys.argv[1].split(';')]; p = int(sys.argv[2]); NP = int(sys.argv[3])
random.seed(int(sys.argv[4])); B = int(sys.argv[5]); wmax = int(sys.argv[6])
D = [int(pari.poldegree(g)) for g in G]; S = [pari.polsym(g, 5*d + 2) for g, d in zip(G, D)]
assert sum(D) == 10
def tr(h, j): return sum(pari.polcoef(h, i, 'x') * S[j][i] for i in range(D[j]))
def test():
    W = [[random.randint(0, wmax) for i in range(d)] for d in D]
    Y = [[[p**W[j][i] * random.randint(-B, B) for i in range(D[j])] for j in range(len(D))] for _ in range(3)]
    # trace-zero: adjust the constant coordinate of factor 0
    for v in Y:
        t = sum(sum(v[j][i] * int(S[j][i]) for i in range(D[j])) for j in range(len(D)))
        v[0][0] = v[0][0] * D[0] * 0 + v[0][0] - pari(t) / D[0]   # rational entry is fine
    T1 = T3 = T5 = 0
    for j, g in enumerate(G):
        e = sum((Y[0][j][i] + pari('y')*Y[1][j][i] + pari('z')*Y[2][j][i]) * pari('x')**i for i in range(D[j])) % g
        e2 = (e*e) % g; e3 = (e2*e) % g; e5 = (e3*e2) % g
        T1 += tr(e, j); T3 += tr(e3, j); T5 += tr(e5, j)
    assert T1 == 0
    if pari.poldegree(pari.numerator(T3), 'y') != 3 or pari.poldegree(pari.numerator(T5), 'y') != 5: return None
    R = pari.polresultant(pari.numerator(T3), pari.numerator(T5), 'y')
    if R == 0 or pari.poldegree(R, 'z') != 15: return None
    if pari.poldegree(pari.gcd(R, pari.deriv(R, 'z')), 'z') > 0: return None
    return len(pari.polrootspadic(R, p, 60))
hits = ok = 0
for k in range(NP):
    r = test()
    if r is None: continue
    ok += 1; hits += (r > 0)
print(f"{sys.argv[1]} p={p} wmax={wmax}: planes {ok}, with a smooth Q_{p}-point: {hits}")
