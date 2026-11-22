# S67.3: explicit Q-points of the Hermite-Joubert cubic X_K = {u in K : Tr u^3 = (Tr u)^3}
# (nonic K, A = K x Q, y = (u, -Tr u)), and of the quintic value on them.
# Usage: python3 xpts67.py <psl|s9|"poly"> <B> [maxprint]
import sys, itertools, numpy as np, cypari
from fractions import Fraction
pari = cypari.pari; pari.allocatemem(2*10**9)
P = {'psl':'x^9 - 3*x^8 - 12000*x^7 - 295072*x^6 + 27805575*x^5 + 1157871573*x^4 + 7683210630*x^3 - 82305140040*x^2 - 848281897593*x - 1186350537195',
     's9':'x^9 - 288*x^7 + 42*x^6 + 30219*x^5 - 10290*x^4 - 1364812*x^3 + 826728*x^2 + 22291201*x - 21772799'}
f = pari(P.get(sys.argv[1], sys.argv[1])); B = int(sys.argv[2]); maxprint = int(sys.argv[3]) if len(sys.argv)>3 else 20
g = pari.polredbest(f)
nf = pari.nfinit(g); n = 9
zk = nf[6]                      # integral basis (polynomials in x)
def mul(a,b): return pari.nfeltmul(nf,a,b)
def tr(a): return int(pari.nfelttrace(nf,a))
E = [pari('vectorv(9,k,k==%d)' % (i+1)) for i in range(n)]
t1 = np.array([tr(E[i]) for i in range(n)], dtype=object)
T3 = np.zeros((n,n,n), dtype=object); T5c = {}
for i in range(n):
    for j in range(i,n):
        eij = mul(E[i],E[j])
        for k in range(j,n):
            v = tr(mul(eij,E[k]))
            for (a,b,c) in set(itertools.permutations((i,j,k))): T3[a,b,c]=v
print('polredbest:', g); print('max |Tr(w_i w_j w_k)| =', max(abs(int(x)) for x in T3.flatten()))
def F3(u):
    s = 0
    for i in range(n):
        if u[i]==0: continue
        for j in range(n):
            if u[j]==0: continue
            s += u[i]*u[j]*sum(T3[i,j,k]*u[k] for k in range(n))
    return s - sum(t1[i]*u[i] for i in range(n))**3
# vectorised search: fix u[0..7] in box, solve cubic in u[8] for rational roots
T3i = T3.astype(np.int64) if max(abs(int(x)) for x in T3.flatten()) < 2**40 else None
sols = []
rng = range(-B, B+1)
for head in itertools.product(rng, repeat=n-1):
    if all(h==0 for h in head): continue
    # cubic c3 x^3 + c2 x^2 + c1 x + c0 in x = u[8]
    u = list(head)+[0]
    c0 = F3(u)
    # coefficients via evaluation at x = 1, -1, 2
    v1 = F3(list(head)+[1]); vm = F3(list(head)+[-1]); v2 = F3(list(head)+[2])
    c2 = (v1+vm)//2 - c0
    odd = (v1-vm)//2               # c3 + c1
    c3 = (v2 - c0 - 4*c2 - 2*odd)//6
    c1 = odd - c3
    poly = pari('Pol([%d,%d,%d,%d])' % (c3,c2,c1,c0))
    if poly == 0: continue
    for fac in pari.factor(poly)[0]:
        if pari.poldegree(fac)==1:
            r = -fac.polcoef(0)/fac.polcoef(1)
            sols.append(tuple(Fraction(int(h)) for h in head)+(Fraction(str(r)),))
    if len(sols) >= 4000: break
# drop u in Q (multiples of 1)
one = pari.nfalgtobasis(nf, 1)
good=[]
for s in sols:
    vec = pari('[' + ','.join(str(x) for x in s) + ']~')
    if pari.matrank(pari.matconcat([vec, one])) == 2: good.append(s)
print('cubic points found (u not in Q):', len(good))
for s in good[:maxprint]:
    vec = pari('[' + ','.join(str(x) for x in s) + ']~'); el = pari.nfbasistoalg(nf, vec)
    cp = pari.charpoly(pari.Mod(pari.lift(el), g)); 
    t = pari.nfelttrace(nf, vec)
    p5 = pari.nfelttrace(nf, pari.nfeltpow(nf, vec, 5)) - t**5
    print([str(x) for x in s], ' Tr u =', t, ' Tr u^5 - (Tr u)^5 =', p5, ' irreducible:', pari.polisirreducible(cp))
