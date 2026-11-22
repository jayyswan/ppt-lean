import cypari, pickle
pari = cypari.pari
pari.allocatemem(2*10**9)
rad = pickle.load(open('radicands13.pkl','rb'))
rad['f4'] = '24*p4 - 19*p2^2'
rad['g6'] = '231*p2^3 - 966*p2*p4 + 1008*p6 - 256*p3^2'
rad['p2'] = 'p2'
rad['h6'] = '-69*p2^3+732*p2*p4+736*p3^2-1440*p6'
Z4B = [['1','I','-1','-I'], ['1','-1','1','-1'], ['1','-I','-1','I']]
Z4C = [1, 2, 3]
V4B = [['1','-1','1','-1'], ['1','1','-1','-1'], ['1','-1','-1','1']]
V4C = [(1,0), (0,1), (1,1)]
GROUPS = {'Z4xZ4': ('Z4','Z4'), 'Z4xV4': ('Z4','V4'), 'V4xZ4': ('V4','Z4'), 'V4xV4': ('V4','V4')}
pari('mons(F,vs)=if(#vs==0,return([[[],F]]));my(v=vs[1],r=List(),d=poldegree(F,v));for(k=0,d,my(c=polcoef(F,k,v));if(c!=0,my(L=mons(c,vs[2..#vs]));for(j=1,#L,listput(r,[concat([k],L[j][1]),L[j][2]]))));Vec(r)')
def setup(a, b, D, group='Z4xZ4'):
    pari('default(seriesprecision,%d)' % (D+1))
    g1, g2 = GROUPS[group]
    B1 = Z4B if g1 == 'Z4' else V4B
    B2 = Z4B if g2 == 'Z4' else V4B
    pi = ['1']*4 + ['0']*4 + ['-4']
    base = [str(a)]*4 + [str(b)]*4 + [str(-4*(a+b))]
    coords = []
    for j in range(9):
        t = base[j] + '+E*(s*(%s)' % pi[j]
        if j < 4:
            t += ''.join('+y%d*(%s)' % (k+1, B1[k][j]) for k in range(3))
        elif j < 8:
            t += ''.join('+y%d*(%s)' % (k+4, B2[k][j-4]) for k in range(3))
        t += ')'
        coords.append(t)
    for k in range(2, 10):
        pari('p%d = (%s) + O(E^%d)' % (k, '+'.join('(%s)^%d' % (c, k) for c in coords), D+1))
def support(name, D):
    S = pari(rad[name].replace('**','^'))
    out = {}
    v = int(pari.valuation(S, pari('E')))
    for d in range(v, D+1):
        F = pari.polcoef(S, d, pari('E'))
        if F == 0: continue
        for m in pari('mons')(F, pari('[s,y1,y2,y3,y4,y5,y6]')):
            out[tuple(int(e) for e in m[0])] = m[1]
    return out
def chars(group):
    g1, g2 = GROUPS[group]
    C = [((0,0),(0,0))]
    for k in range(3):
        c1 = (Z4C[k], 0) if g1 == 'Z4' else V4C[k]
        C.append((c1, (0,0)))
    for k in range(3):
        c2 = (Z4C[k], 0) if g2 == 'Z4' else V4C[k]
        C.append(((0,0), c2))
    mods = ((4,1) if g1 == 'Z4' else (2,2), (4,1) if g2 == 'Z4' else (2,2))
    return C, mods
